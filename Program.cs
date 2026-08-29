using System.Diagnostics;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Runtime.InteropServices.WindowsRuntime;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Microsoft.Web.WebView2.Core;
using Microsoft.Web.WebView2.WinForms;
using Microsoft.Win32;
using SDL2;
using Windows.Graphics.Imaging;
using Windows.Media.Ocr;

namespace HD2_Helper
{
    internal class Program
    {
        [STAThread]
        static void Main()
        {
            using (Mutex mutex = new Mutex(true, "HD2_Helper_Unique", out bool createdNew))
            {
                if (!createdNew)
                {
                    MessageBox.Show("이미 프로그램이 실행 중입니다.", "알림", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                    return;
                }

                NativeLibrary.SetDllImportResolver(typeof(SDL).Assembly, (libraryName, assembly, searchPath) =>
                {
                    if (libraryName == "SDL2")
                        return NativeLibrary.Load("SDL2.dll", assembly, searchPath);
                    return IntPtr.Zero;
                });

                ApplicationConfiguration.Initialize();
                MainForm mainForm = new MainForm();
                Application.Run();
            }
        }
    }

    public class MainForm : Form
    {
        private static readonly string AppDataPath = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "HD2 Helper");
        private static readonly string SettingsPath = Path.Combine(AppDataPath, "settings.ini");
        private static readonly string DisabledItemsPath = Path.Combine(AppDataPath, "disabled.ini");
        private static readonly string PresetsPath = Path.Combine(AppDataPath, "presets.json");

        private WebView2? _webView;
        private OverlayForm? _overlayForm;
        private CancellationTokenSource? _padLoopCts;
        private InputHookManager? _inputHook;
        private OcrEngine? _ocrEngine;

        private const int BaseClientWidth = 950;
        private const int BaseClientHeight = 590;
        private const int BaseReferenceWidth = 1920;
        private const int BaseReferenceHeight = 1080;
        private const double MinClientScale = 0.5;
        private bool _isAdjustingClientSize;

        private static List<(string Type, string Category, string Name)> _parsedData = new();
        private static Dictionary<string, Image?> _imageCache = new();
        private static Dictionary<string, string[]> _sequenceMap = new();

        private static string?[] _currentSlots = new string?[10];
        private static string?[] _currentLoadoutSlots = new string?[4];
        private static HashSet<string> _disabledItems = new();

        private static readonly Dictionary<int, uint> _slotKey = new();
        private static readonly Dictionary<uint, (string Trigger, float Threshold)> _mouseKey = new();

        private static string _stratagemType = "Hold";
        private static readonly Dictionary<string, uint> _stratagemKey = new()
        {
            ["start"] = (uint)Keys.LControlKey,
            ["up"] = (uint)Keys.W,
            ["down"] = (uint)Keys.S,
            ["left"] = (uint)Keys.A,
            ["right"] = (uint)Keys.D,
        };

        private static int _inputDelay = 30;
        private static uint _autoSelectKey = (uint)Keys.F1;
        private static uint _overlayKey = (uint)Keys.MButton;
        private static uint _reinforceKey = (uint)Keys.XButton1;
        private static uint _chatKey = (uint)Keys.Enter;
        private static bool _stratagemCompactLayout;

        private static bool _isChat;
        private static bool _isPad;
        private static bool _isWaitingForKey;
        private static string? _waitingKeyTarget;
        private static uint _captureModsHeld;         // modifier flags currently held during key capture
        private static bool _captureMultipleMods;     // true when >1 modifier was held at once during capture

        // Shortcut combo encoding: modifier flags live in bits 16-20, the virtual key in bits 0-15.
        private const uint ModCtrl = 0x00010000;
        private const uint ModAlt = 0x00020000;
        private const uint ModShift = 0x00040000;
        private const uint ModWin = 0x00080000;
        private const uint ModSpace = 0x00100000;
        private const uint KeyMask = 0x0000FFFF;
        private static uint _overlayActiveKey;
        private int _isSending = 0;

        public class InputEventArgs : EventArgs
        {
            public uint VirtualKey { get; }
            public bool IsDown { get; }
            public InputEventArgs(uint vk, bool isDown)
            {
                VirtualKey = vk;
                IsDown = isDown;
            }
        }

        public enum PadButton : uint
        {
            L1 = 0x1001, R1, L2, R2, L3, R3,
            DUp, DDown, DLeft, DRight,
            PadA, PadB, PadX, PadY,
            PadStart, PadBack,
        }

        #region WinAPI
        [DllImport("user32.dll")]
        private static extern IntPtr GetForegroundWindow();

        [DllImport("user32.dll", SetLastError = true, CharSet = CharSet.Auto)]
        private static extern int GetClassName(IntPtr hWnd, StringBuilder lpClassName, int nMaxCount);

        [DllImport("user32.dll")]
        private static extern bool GetClientRect(IntPtr hWnd, out Rectangle lpRect);

        [DllImport("user32.dll")]
        private static extern bool ClientToScreen(IntPtr hWnd, ref Point lpPoint);

        [DllImport("user32.dll")]
        private static extern void keybd_event(uint bVk, uint bScan, uint dwFlags, UIntPtr dwExtraInfo);

        [DllImport("user32.dll")]
        private static extern short GetAsyncKeyState(int vKey);

        [DllImport("user32.dll")]
        private static extern void mouse_event(uint dwFlags, uint dx, uint dy, uint dwData, IntPtr dwExtraInfo);
        #endregion

        public MainForm()
        {
            Icon = Icon.ExtractAssociatedIcon(Application.ExecutablePath);
            Text = "헬다이버즈2 보조 기구";
            FormBorderStyle = FormBorderStyle.Sizable;
            MaximizeBox = false;
            BackColor = Color.FromArgb(0x22, 0x22, 0x22);
            ClientSize = GetInitialClientSize();
            MinimumSize = SizeFromClientSize(new Size((int)Math.Round(BaseClientWidth * MinClientScale), (int)Math.Round(BaseClientHeight * MinClientScale)));
            Resize += (_, _) => KeepClientAspectRatio();

            StartPosition = FormStartPosition.Manual;
            Rectangle area = Screen.PrimaryScreen!.WorkingArea;
            Left = area.Left + (area.Width - Width) / 2;
            Top = area.Top + (area.Height - Height) / 2;

            _webView = new WebView2();
            _webView.Dock = DockStyle.Fill;
            _webView.DefaultBackgroundColor = Color.FromArgb(0x22, 0x22, 0x22);
            Controls.Add(_webView);

            Initialization();
        }

        protected override void WndProc(ref Message m)
        {
            const int WM_NCHITTEST = 0x84;
            const int HTTOP = 12;
            const int HTBOTTOM = 15;
            const int HTTOPLEFT = 13;
            const int HTTOPRIGHT = 14;
            const int HTBOTTOMLEFT = 16;
            const int HTBOTTOMRIGHT = 17;

            base.WndProc(ref m);

            if (m.Msg == WM_NCHITTEST)
            {
                int result = m.Result.ToInt32();

                if (result == HTTOP || result == HTBOTTOM ||
                    result == HTTOPLEFT || result == HTBOTTOMLEFT ||
                    result == HTTOPRIGHT || result == HTBOTTOMRIGHT)
                    m.Result = (IntPtr)1;
            }
        }

        private static Size GetInitialClientSize()
        {
            Rectangle bounds = Screen.PrimaryScreen!.Bounds;
            double scale = Math.Min(
                (double)bounds.Width / BaseReferenceWidth,
                (double)bounds.Height / BaseReferenceHeight
            );

            scale = Math.Max(scale, MinClientScale);
            return new Size(
                (int)Math.Round(BaseClientWidth * scale),
                (int)Math.Round(BaseClientHeight * scale)
            );
        }

        private void KeepClientAspectRatio()
        {
            if (_isAdjustingClientSize || WindowState != FormWindowState.Normal) return;

            int width = ClientSize.Width;
            int height = ClientSize.Height;
            if (width <= 0 || height <= 0) return;

            int minWidth = (int)Math.Round(BaseClientWidth * MinClientScale);
            int minHeight = (int)Math.Round(BaseClientHeight * MinClientScale);
            double targetRatio = (double)BaseClientWidth / BaseClientHeight;
            width = Math.Max(width, minWidth);
            height = Math.Max(height, minHeight);
            int targetHeight = (int)Math.Round(width / targetRatio);
            int targetWidth = (int)Math.Round(height * targetRatio);

            Size nextSize = Math.Abs(targetHeight - height) <= Math.Abs(targetWidth - width)
                ? new Size(width, targetHeight)
                : new Size(targetWidth, height);

            if (nextSize == ClientSize) return;

            _isAdjustingClientSize = true;
            ClientSize = nextSize;
            _isAdjustingClientSize = false;
        }

        private async void Initialization()
        {
            // 데이터 불러오기
            LoadDatabase();
            LoadUserSetting();
            LoadSetting();

            // 업데이트 체크
            bool isUpdating = await CheckForUpdates();
            if (isUpdating) return;

            // 입력 처리
            this.Shown += (s, e) =>
            {
                _inputHook = new InputHookManager();
                _inputHook.OnInputEvent += (hookSender, inputArgs) =>
                {
                    if (IsDisposed) return;
                    this.BeginInvoke(new Action(() => HandleHookInput(inputArgs)));
                };
            };

            // 패드
            await GamepadReader.InitializeAsync();
            StartPadLoop();

            // OCR
            WarmupOcr();

            // 웹뷰
            InitializeWebView();
        }
       
        private void LoadDatabase(string path = "database.json")
        {
            if (!File.Exists(path))
            {
                MessageBox.Show($"{path} 파일을 찾을 수 없습니다.\n프로그램을 종료합니다.", "오류", MessageBoxButtons.OK, MessageBoxIcon.Error);
                this.OnFormClosed(null!);
                return;
            }

            try
            {
                var json = File.ReadAllText(path);
                var root = JsonSerializer.Deserialize<Dictionary<string, Dictionary<string, List<JsonElement>>>>(json);

                if (root != null)
                {
                    foreach (var type in root)
                    {
                        foreach (var subCat in type.Value)
                        {
                            string subCategoryName = subCat.Key;

                            foreach (var item in subCat.Value)
                            {
                                string name = item.GetProperty("Name").GetString() ?? "";

                                if (type.Key == "스트라타젬" && item.TryGetProperty("Sequence", out JsonElement seqElement))
                                {
                                    _sequenceMap[name] = seqElement.EnumerateArray()
                                        .Select(x => x.GetString()?.ToLowerInvariant() ?? "")
                                        .ToArray();
                                }

                                _parsedData.Add((type.Key, subCategoryName, name));
                            }
                        }
                    }
                }
            }
            catch (JsonException ex)
            {
                MessageBox.Show($"JSON 파일 문법 오류:\n{ex.Message}\n프로그램을 종료합니다.", "오류", MessageBoxButtons.OK, MessageBoxIcon.Error);
                this.OnFormClosed(null!);
            }
        }

        private void LoadUserSetting()
        {
            List<FileInfo> configCandidates = new();

            string localSavesPath = Path.Combine(
                Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData),
                @"Arrowhead\Helldivers2\saves"
            );

            if (Directory.Exists(localSavesPath))
            {
                configCandidates.AddRange(
                    new DirectoryInfo(localSavesPath).GetFiles("*_input_settings.config")
                        .Where(f => f.Exists && f.Length > 0));
            }

            using (var steamKey = Registry.CurrentUser.OpenSubKey(@"Software\Valve\Steam"))
            {
                string? steamPath = steamKey?.GetValue("SteamPath") as string;

                if (!string.IsNullOrWhiteSpace(steamPath))
                {
                    string userdataPath = Path.Combine(steamPath, "userdata");

                    if (Directory.Exists(userdataPath))
                    {
                        foreach (string userDir in Directory.GetDirectories(userdataPath))
                        {
                            string configPath = Path.Combine(userDir, "553850", "remote", "input_settings.config");

                            if (File.Exists(configPath))
                            {
                                var fi = new FileInfo(configPath);

                                if (fi.Length > 0)
                                    configCandidates.Add(fi);
                            }
                        }
                    }
                }
            }

            var latestConfig = configCandidates
                .OrderByDescending(f => f.LastWriteTimeUtc)
                .FirstOrDefault();

            if (latestConfig == null)
                return;

            string rawConfig = File.ReadAllText(latestConfig.FullName);

            int avatarIdx = rawConfig.IndexOf("Avatar = {");
            string avatarBlock = (avatarIdx != -1) ? rawConfig.Substring(avatarIdx) : "";

            int playerIdx = rawConfig.IndexOf("Player = {");
            string playerBlock = (playerIdx != -1) ? rawConfig.Substring(playerIdx) : "";

            int stratagemIdx = rawConfig.IndexOf("Stratagem = {");
            string stratagemBlock = (stratagemIdx != -1) ? rawConfig.Substring(stratagemIdx) : "";

            var keys = new[] { "Fire", "Aim", "OpenChat", "Start", "Up", "Left", "Down", "Right" };

            foreach (var k in keys)
            {
                string targetBlock = (k == "Fire" || k == "Aim") ? avatarBlock : (k == "OpenChat") ? playerBlock : stratagemBlock;

                if (string.IsNullOrEmpty(targetBlock) || !targetBlock.Contains($"{k} ="))
                {
                    if (k == "Fire") _mouseKey[(uint)Keys.LButton] = ("Hold", 0);
                    else if (k == "Aim") _mouseKey[(uint)Keys.RButton] = ("Hold", 0);
                    continue;
                }

                var keyBlockMatch = Regex.Match(targetBlock, k + @"\s*=\s*\[(.*?)\]", RegexOptions.Singleline | RegexOptions.IgnoreCase);
                if (!keyBlockMatch.Success) continue;

                var matches = Regex.Matches(keyBlockMatch.Groups[1].Value, @"\{([\s\S]*?)\}", RegexOptions.Singleline);

                foreach (Match braceMatch in matches)
                {
                    string inner = braceMatch.Groups[1].Value;

                    var triggerMatch = Regex.Match(inner, @"trigger\s*=\s*""([^""]+)""", RegexOptions.IgnoreCase);
                    var deviceMatch = Regex.Match(inner, @"device_type\s*=\s*""(Keyboard|Mouse)""", RegexOptions.IgnoreCase);
                    var inputMatch = Regex.Match(inner, @"input\s*=\s*""([^""]+)""", RegexOptions.IgnoreCase);
                    var thresholdMatch = Regex.Match(inner, @"threshold\s*=\s*([0-9.]+)", RegexOptions.IgnoreCase);

                    if (!deviceMatch.Success || !inputMatch.Success || !triggerMatch.Success || !thresholdMatch.Success)
                        continue;

                    string key = k.ToLower();
                    string device = deviceMatch.Groups[1].Value.ToLower();
                    string input = inputMatch.Groups[1].Value.ToLower();
                    string trigger = triggerMatch.Groups[1].Value;
                    float threshold = float.Parse(thresholdMatch.Groups[1].Value) * 1000f;
                    var vk = ParseInputKey(input);

                    if (key == "fire" || key == "aim")
                    {
                        if (device == "mouse" && input.Contains("mousebutton") && vk.HasValue)
                        {
                            _mouseKey[vk.Value] = (trigger, threshold);
                        }
                        continue;
                    }

                    if (vk.HasValue)
                    {
                        if (key == "openchat") _chatKey = vk.Value;
                        else _stratagemKey[key] = vk.Value;
                    }

                    if (key == "start")
                        _stratagemType = trigger;

                    break;
                }
            }
        }   

        private async Task<bool> CheckForUpdates()
        {
            try
            {
                using var client = new HttpClient();
                client.DefaultRequestHeaders.UserAgent.ParseAdd("HD2-Helper");

                string url = "https://api.github.com/repos/ChubbyMaru/HD2-Helper/releases/latest";
                var json = await client.GetStringAsync(url);

                using var doc = JsonDocument.Parse(json);
                string latestVersionStr = doc.RootElement
                    .GetProperty("tag_name")
                    .GetString()!
                    .TrimStart('v');

                var latestVersion = new Version(latestVersionStr);
                var currentVersion = new Version(Application.ProductVersion.Split('+')[0]);

                if (latestVersion > currentVersion)
                {
                    var result = MessageBox.Show(
                        this,
                        $"새 버전 {latestVersion} 발견!\nGitHub 페이지로 이동하시겠습니까?",
                        "업데이트",
                        MessageBoxButtons.YesNo,
                        MessageBoxIcon.Information);

                    if (result == DialogResult.Yes)
                    {
                        Process.Start(new ProcessStartInfo
                        {
                            FileName = "https://github.com/ChubbyMaru/HD2-Helper/releases/latest",
                            UseShellExecute = true
                        });

                        this.OnFormClosed(null!);
                        return true;
                    }
                }
            }
            catch { }
            return false;
        }

        private async void InitializeWebView()
        {
            try
            {
                string localAppData = Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData);
                string userDataFolder = Path.Combine(localAppData, "HD2_Helper_Cache");
                string exeFolder = AppDomain.CurrentDomain.BaseDirectory;

                var options = new CoreWebView2EnvironmentOptions("--disable-gpu --disable-gpu-compositing");
                var env = await WithTimeout(
                    CoreWebView2Environment.CreateAsync(userDataFolder: userDataFolder, options: options),
                    TimeSpan.FromSeconds(10)
                );

                await WithTimeout(
                    _webView!.EnsureCoreWebView2Async(env),
                    TimeSpan.FromSeconds(10));

                var settings = _webView.CoreWebView2.Settings;
                settings.AreDefaultContextMenusEnabled = false;
                settings.AreDevToolsEnabled = false;
                settings.IsStatusBarEnabled = false;
                settings.IsZoomControlEnabled = false;
                settings.AreBrowserAcceleratorKeysEnabled = false;

                _webView.CoreWebView2.SetVirtualHostNameToFolderMapping("hd2.local", exeFolder, CoreWebView2HostResourceAccessKind.Allow);
                _webView.CoreWebView2.WebMessageReceived += OnWebMessageReceived;

                var assembly = System.Reflection.Assembly.GetEntryAssembly()!;
                using var stream = assembly.GetManifestResourceStream(Array.Find(assembly.GetManifestResourceNames(), n => n.EndsWith("index.html"))!)!;
                string htmlContent = new StreamReader(stream).ReadToEnd();

                _webView.CoreWebView2.NavigateToString(htmlContent);
            }
            catch
            {
                MessageBox.Show(
                    "WebView2 런타임이 없거나 초기화에 실패했습니다.\n\n" +
                    "확인을 누르면 WebView2 런타임 설치 파일을 다운로드합니다.\n" +
                    "다운로드한 설치 파일은 관리자 권한으로 실행해 주세요.",
                    "오류",
                    MessageBoxButtons.OK,
                    MessageBoxIcon.Error);

                Process.Start(new ProcessStartInfo
                {
                    FileName = "https://go.microsoft.com/fwlink/p/?LinkId=2124703",
                    UseShellExecute = true
                });

                this.OnFormClosed(null!);
            }
        }

        private static async Task<T> WithTimeout<T>(Task<T> task, TimeSpan timeout)
        {
            Task delayTask = Task.Delay(timeout);
            Task completedTask = await Task.WhenAny(task, delayTask);

            if (completedTask == delayTask)
                throw new TimeoutException();

            return await task;
        }

        private static async Task WithTimeout(Task task, TimeSpan timeout)
        {
            Task delayTask = Task.Delay(timeout);
            Task completedTask = await Task.WhenAny(task, delayTask);

            if (completedTask == delayTask)
                throw new TimeoutException();

            await task;
        }

        private void OnWebMessageReceived(object? sender, CoreWebView2WebMessageReceivedEventArgs e)
        {
            HandleWebJsonMessage(e.WebMessageAsJson);
        }

        private void HandleWebJsonMessage(string json)
        {
            try
            {
                using var doc = JsonDocument.Parse(json);
                if (!doc.RootElement.TryGetProperty("type", out var typeElement)) return;

                string? type = typeElement.GetString();
                if (type == "LOAD_DISABLED_ITEMS")
                {
                    SendDisabledItemsToWeb();
                }
                else if (type == "LOAD_PRESETS")
                {
                    SendPresetsToWeb();
                }
                else if (type == "LOAD_SETTINGS")
                {
                    SendSettingsToWeb();
                }
                else if (type == "IMAGE_CACHE_READY")
                {
                    this.Show();
                    this.Activate();
                }
                else if (type == "SET_INPUT_DELAY")
                {
                    if (doc.RootElement.TryGetProperty("value", out var valueElement) && valueElement.TryGetInt32(out int value))
                    {
                        _inputDelay = Math.Clamp(value, 30, 100);
                        SaveSetting();
                        SendSettingsToWeb();
                    }
                }
                else if (type == "START_KEY_CAPTURE")
                {
                    if (doc.RootElement.TryGetProperty("target", out var targetElement))
                    {
                        string? target = targetElement.GetString();
                        if (IsValidSettingsKeyTarget(target))
                        {
                            _waitingKeyTarget = target;
                            _isWaitingForKey = true;
                            ResetCaptureModifiers();
                            SendSettingsToWeb();
                        }
                    }
                }
                else if (type == "SET_STRATAGEM_LAYOUT")
                {
                    if (doc.RootElement.TryGetProperty("compact", out var compactElement))
                    {
                        _stratagemCompactLayout = compactElement.GetBoolean();
                        SaveSetting();
                        SendSettingsToWeb();
                    }
                }
                else if (type == "CANCEL_KEY_CAPTURE")
                {
                    _isWaitingForKey = false;
                    _waitingKeyTarget = null;
                    ResetCaptureModifiers();
                    SendSettingsToWeb();
                }
                else if (type == "SAVE_DISABLED_ITEMS")
                {
                    var items = doc.RootElement.TryGetProperty("items", out var itemsElement) && itemsElement.ValueKind == JsonValueKind.Array
                        ? itemsElement.EnumerateArray()
                            .Select(item => item.GetString())
                            .Where(item => !string.IsNullOrWhiteSpace(item))
                            .Select(item => item!.Trim())
                            .Distinct()
                            .OrderBy(item => item)
                            .ToArray()
                        : Array.Empty<string>();

                    _disabledItems = items.ToHashSet();
                    SaveDisabledItems(items);
                }
                else if (type == "SAVE_PRESETS")
                {
                    if (doc.RootElement.TryGetProperty("presets", out var presetsElement) && presetsElement.ValueKind == JsonValueKind.Array)
                    {
                        SavePresets(presetsElement.GetRawText());
                    }
                }
                else if (type == "CURRENT_LOADOUT")
                {
                    UpdateCurrentLoadoutFromWeb(doc.RootElement);
                }
            }
            catch { }
        }

        private void UpdateCurrentLoadoutFromWeb(JsonElement root)
        {
            if (!root.TryGetProperty("loadout", out var loadoutElement) || loadoutElement.ValueKind != JsonValueKind.Object)
                return;

            var slots = new string?[10];
            if (loadoutElement.TryGetProperty("stratagems", out var stratagemsElement) && stratagemsElement.ValueKind == JsonValueKind.Array)
            {
                int index = 0;
                foreach (var item in stratagemsElement.EnumerateArray())
                {
                    if (index >= slots.Length) break;

                    string? name = item.GetString();
                    slots[index++] = name;

                    if (!string.IsNullOrEmpty(name))
                    {
                        GetStratagemImage(name);
                    }
                }
            }

            _currentSlots = slots;
            _currentLoadoutSlots = new[]
            {
                GetLoadoutString(loadoutElement, "armor"),
                GetLoadoutString(loadoutElement, "primary"),
                GetLoadoutString(loadoutElement, "secondary"),
                GetLoadoutString(loadoutElement, "grenade")
            };
        }

        private static string? GetLoadoutString(JsonElement loadoutElement, string propertyName)
        {
            return loadoutElement.TryGetProperty(propertyName, out var property) && property.ValueKind == JsonValueKind.String
                ? property.GetString()
                : null;
        }


        private static string[] LoadDisabledItems()
        {
            if (!File.Exists(DisabledItemsPath))
            {
                _disabledItems.Clear();
                return Array.Empty<string>();
            }

            var items = File.ReadAllLines(DisabledItemsPath, Encoding.UTF8)
                .Select(line => line.Trim())
                .Where(line => line.Length > 0 && !line.StartsWith(";") && !line.StartsWith("#"))
                .Distinct()
                .ToArray();

            _disabledItems = items.ToHashSet(StringComparer.Ordinal);
            return items;
        }

        private static void SaveDisabledItems(IEnumerable<string> items)
        {
            Directory.CreateDirectory(AppDataPath);
            File.WriteAllLines(DisabledItemsPath, items, Encoding.UTF8);
        }

        private void SendDisabledItemsToWeb()
        {
            if (_webView?.CoreWebView2 == null) return;

            var payload = new
            {
                type = "DISABLED_ITEMS_LOADED",
                items = LoadDisabledItems()
            };

            _webView.CoreWebView2.PostWebMessageAsJson(JsonSerializer.Serialize(payload));
        }

        private static string LoadPresetsJson()
        {
            if (!File.Exists(PresetsPath)) return "[]";

            string json = File.ReadAllText(PresetsPath, Encoding.UTF8);
            if (string.IsNullOrWhiteSpace(json)) return "[]";

            using var doc = JsonDocument.Parse(json);
            return doc.RootElement.ValueKind == JsonValueKind.Array ? json : "[]";
        }

        private static void SavePresets(string json)
        {
            using var doc = JsonDocument.Parse(json);
            if (doc.RootElement.ValueKind != JsonValueKind.Array) return;

            Directory.CreateDirectory(AppDataPath);
            File.WriteAllText(PresetsPath, json, Encoding.UTF8);
        }

        private static void LoadSetting()
        {
            if (!File.Exists(SettingsPath)) return;

            foreach (string rawLine in File.ReadAllLines(SettingsPath, Encoding.UTF8))
            {
                string line = rawLine.Trim();
                if (line.Length == 0 || line.StartsWith(";") || line.StartsWith("#")) continue;

                int separator = line.IndexOf('=');
                if (separator <= 0) continue;

                string key = line[..separator].Trim();
                string value = line[(separator + 1)..].Trim();
                if (!uint.TryParse(value, out uint vk) && !key.Equals("inputDelay", StringComparison.OrdinalIgnoreCase))
                    continue;

                if (key.Equals("inputDelay", StringComparison.OrdinalIgnoreCase))
                {
                    if (int.TryParse(value, out int delay)) _inputDelay = Math.Clamp(delay, 30, 100);
                }
                else if (key.Equals("stratagemCompactLayout", StringComparison.OrdinalIgnoreCase))
                {
                    _stratagemCompactLayout = vk != 0;
                }
                else if (key.Equals("autoSelectKey", StringComparison.OrdinalIgnoreCase))
                {
                    _autoSelectKey = vk;
                }
                else if (key.Equals("overlayKey", StringComparison.OrdinalIgnoreCase))
                {
                    _overlayKey = vk;
                }
                else if (key.Equals("reinforceKey", StringComparison.OrdinalIgnoreCase))
                {
                    _reinforceKey = vk;
                }
                else if (key.StartsWith("slot", StringComparison.OrdinalIgnoreCase)
                    && int.TryParse(key[4..], out int slot)
                    && slot >= 1
                    && slot <= 10)
                {
                    if (vk == 0) _slotKey.Remove(slot - 1);
                    else _slotKey[slot - 1] = vk;
                }
            }
        }

        private static void SaveSetting()
        {
            Directory.CreateDirectory(AppDataPath);

            var lines = new List<string>
            {
                $"inputDelay={Math.Clamp(_inputDelay, 30, 100)}",
                $"stratagemCompactLayout={(_stratagemCompactLayout ? 1 : 0)}",
                $"autoSelectKey={_autoSelectKey}",
                $"overlayKey={_overlayKey}",
                $"reinforceKey={_reinforceKey}"
            };

            for (int slot = 1; slot <= 10; slot++)
            {
                lines.Add($"slot{slot}={(_slotKey.TryGetValue(slot - 1, out uint key) ? key : 0)}");
            }

            File.WriteAllLines(SettingsPath, lines, Encoding.UTF8);
        }

        private static bool IsValidSettingsKeyTarget(string? target)
        {
            if (string.IsNullOrWhiteSpace(target)) return false;
            if (target is "autoSelectKey" or "overlayKey" or "reinforceKey") return true;
            return target.StartsWith("slot", StringComparison.OrdinalIgnoreCase)
                && int.TryParse(target[4..], out int slot)
                && slot >= 1
                && slot <= 10;
        }

        private void AssignCapturedSettingsKey(uint vkCode)
        {
            if ((vkCode & KeyMask) == (uint)Keys.LButton)
                return;

            if ((vkCode & KeyMask) == (uint)Keys.RButton)
                vkCode = 0;

            string? target = _waitingKeyTarget;
            _isWaitingForKey = false;
            _waitingKeyTarget = null;
            ResetCaptureModifiers();

            if (!IsValidSettingsKeyTarget(target)) return;

            if (vkCode != 0)
            {
                if (_autoSelectKey == vkCode) _autoSelectKey = 0;
                if (_overlayKey == vkCode) _overlayKey = 0;
                if (_reinforceKey == vkCode) _reinforceKey = 0;

                var slotKeys = _slotKey.Keys.ToList();
                foreach (var key in slotKeys)
                {
                    if (_slotKey[key] == vkCode)
                    {
                        _slotKey.Remove(key);
                    }
                }
            }

            if (target == "autoSelectKey") _autoSelectKey = vkCode;
            else if (target == "overlayKey") _overlayKey = vkCode;
            else if (target == "reinforceKey") _reinforceKey = vkCode;
            else if (target!.StartsWith("slot", StringComparison.OrdinalIgnoreCase)
                && int.TryParse(target[4..], out int slot)
                && slot >= 1
                && slot <= 10)
            {
                if (vkCode == 0) _slotKey.Remove(slot - 1);
                else _slotKey[slot - 1] = vkCode;
            }

            SaveSetting();
            SendSettingsToWeb();
        }

        private void SendPresetsToWeb()
        {
            if (_webView?.CoreWebView2 == null) return;

            using var presetsDoc = JsonDocument.Parse(LoadPresetsJson());
            var payload = new
            {
                type = "PRESETS_LOADED",
                presets = presetsDoc.RootElement.Clone()
            };

            _webView.CoreWebView2.PostWebMessageAsJson(JsonSerializer.Serialize(payload));
        }

        private void SendSettingsToWeb()
        {
            if (_webView?.CoreWebView2 == null) return;

            var slotKeys = Enumerable.Range(1, 10)
                .Select(slot => new
                {
                    slot,
                    target = $"slot{slot}",
                    key = _slotKey.TryGetValue(slot - 1, out uint value) ? value : 0,
                    name = GetKeyName(_slotKey.TryGetValue(slot - 1, out uint keyName) ? keyName : 0)
                })
                .ToArray();

            var payload = new
            {
                type = "SETTINGS_LOADED",
                inputDelay = Math.Clamp(_inputDelay, 30, 100),
                stratagemCompactLayout = _stratagemCompactLayout,
                waitingTarget = _isWaitingForKey ? _waitingKeyTarget : null,
                keys = new
                {
                    autoSelectKey = new { value = _autoSelectKey, name = GetKeyName(_autoSelectKey) },
                    overlayKey = new { value = _overlayKey, name = GetKeyName(_overlayKey) },
                    reinforceKey = new { value = _reinforceKey, name = GetKeyName(_reinforceKey) },
                    slots = slotKeys
                }
            };

            _webView.CoreWebView2.PostWebMessageAsJson(JsonSerializer.Serialize(payload));
        }

        private async void WarmupOcr()
        {
            try
            {
                _ocrEngine = OcrEngine.TryCreateFromLanguage(new Windows.Globalization.Language("ko-KR"));
                if (_ocrEngine == null) return;

                using var dummy = new SoftwareBitmap(BitmapPixelFormat.Bgra8, 10, 10, BitmapAlphaMode.Premultiplied);
                await _ocrEngine.RecognizeAsync(dummy);
            }
            catch
            {
                _ocrEngine = null;
            }
        }

        private Image? GetStratagemImage(string name)
        {
            if (_imageCache.TryGetValue(name, out var cached))
                return cached;

            string path = Path.Combine(AppContext.BaseDirectory, "images", "stratagems", $"{name}.png");
            if (!File.Exists(path))
            {
                _imageCache[name] = null;
                return null;
            }

            using (var original = Image.FromFile(path))
            {
                var resized = new Bitmap(original, new Size(100, 100));
                _imageCache[name] = resized;
                return resized;
            }
        }

        public static bool IsGameActive()
        {
            IntPtr hwnd = GetForegroundWindow();
            if (hwnd == IntPtr.Zero) return false;

            var className = new StringBuilder(256);
            return GetClassName(hwnd, className, className.Capacity) != 0 &&
                   className.ToString() == "stingray_window";
        }

        private void StartPadLoop()
        {
            _padLoopCts?.Cancel();

            _padLoopCts = new CancellationTokenSource();
            var token = _padLoopCts.Token;

            Task.Run(async () =>
            {
                while (!token.IsCancellationRequested)
                {
                    var padEvents = GamepadReader.GetButtonEvents();
                    foreach (var ev in padEvents)
                    {
                        uint pressedPadButton = (uint)ev.Button;

                        if (_isWaitingForKey && Form.ActiveForm is MainForm && ev.Pressed)
                        {
                            this.BeginInvoke(new Action(() =>
                            {
                                AssignCapturedSettingsKey(pressedPadButton);
                            }));
                            continue;
                        }

                        if (pressedPadButton == _overlayKey)
                        {
                            this.BeginInvoke(new Action(() =>
                            {
                                if (ev.Pressed) OverlayShow();
                                else OverlayHide();
                            }));
                        }
                        else if (pressedPadButton == _autoSelectKey && ev.Pressed)
                        {
                            TriggerAutoSelection();
                        }
                        else if (pressedPadButton == _reinforceKey && ev.Pressed)
                        {
                            TriggerStratagem(-1);
                        }
                        else if (ev.Pressed)
                        {
                            foreach (var pair in _slotKey)
                            {
                                if (pressedPadButton == pair.Value)
                                {
                                    TriggerStratagem(pair.Key);
                                    break;
                                }
                            }
                        }
                    }

                    var stick = GamepadReader.GetRightStick();
                    if (_overlayForm != null)
                    {
                        float speed = 30f;
                        float moveX = stick.dx * speed;
                        float moveY = stick.dy * speed;

                        int dx = (int)Math.Round(moveX);
                        int dy = (int)Math.Round(moveY);

                        if (dx != 0 || dy != 0)
                            mouse_event(0x0001, (uint)dx, (uint)dy, 0, IntPtr.Zero);
                    }

                    await Task.Delay(16, token);
                }
            }, token);
        }

        private void HandleHookInput(InputEventArgs e)
        {
            uint vkCode = e.VirtualKey;

            if (_isWaitingForKey && Form.ActiveForm is MainForm)
            {
                if (IsModifierKey(vkCode))
                {
                    if (e.IsDown)
                    {
                        // Space pressed while another modifier is held -> Space is the base key (e.g. Ctrl+Space).
                        if (vkCode == (uint)Keys.Space && (_captureModsHeld & ~ModSpace) != 0)
                        {
                            ResetCaptureModifiers();
                            AssignCapturedSettingsKey(ComposeCombo(vkCode));
                            return;
                        }
                        // Modifier held: wait for a real key (combo) or its own release (standalone).
                        uint flag = ModFlagOf(vkCode);
                        if ((_captureModsHeld & ~flag) != 0) _captureMultipleMods = true;
                        _captureModsHeld |= flag;
                        return;
                    }
                    // Modifier released. Commit standalone only if it was the sole modifier and none is still held.
                    _captureModsHeld &= ~ModFlagOf(vkCode);
                    if (_captureModsHeld == 0 && !_captureMultipleMods)
                        AssignCapturedSettingsKey(vkCode);
                    return;
                }

                if (e.IsDown)
                {
                    // Real key pressed while a modifier is held -> compose the combo.
                    ResetCaptureModifiers();
                    AssignCapturedSettingsKey(ComposeCombo(vkCode));
                }
                return;
            }

            uint currentMods = GetModifiersFor(vkCode);

            if (e.IsDown)
            {
                if (MatchesBinding(_overlayKey, vkCode, currentMods, exactOnly: false))
                {
                    _overlayActiveKey = vkCode;
                    OverlayShow();
                }
            }
            else if (_overlayActiveKey == vkCode)
            {
                _overlayActiveKey = 0;
                OverlayHide();
            }

            if (!e.IsDown)
                return;

            // Combo bindings (with modifiers) take priority over legacy plain keys on the same key.
            if (TryFireSettingsAction(vkCode, currentMods, exactOnly: true)) return;
            TryFireSettingsAction(vkCode, currentMods, exactOnly: false);
        }

        private static bool IsModifierKey(uint vk)
        {
            return vk is (uint)Keys.ShiftKey or (uint)Keys.ControlKey or (uint)Keys.Menu
                or (uint)Keys.LShiftKey or (uint)Keys.RShiftKey
                or (uint)Keys.LControlKey or (uint)Keys.RControlKey
                or (uint)Keys.LMenu or (uint)Keys.RMenu
                or (uint)Keys.LWin or (uint)Keys.RWin
                or (uint)Keys.Space;
        }

        private static bool IsKeyDown(int vk)
        {
            return (GetAsyncKeyState(vk) & 0x8000) != 0;
        }

        private static uint GetCurrentModifiers()
        {
            uint mods = 0;
            if (IsKeyDown(0x11) || IsKeyDown(0xA2) || IsKeyDown(0xA3)) mods |= ModCtrl;  // Ctrl / LCtrl / RCtrl
            if (IsKeyDown(0x12) || IsKeyDown(0xA4) || IsKeyDown(0xA5)) mods |= ModAlt;   // Alt / LAlt / RAlt
            if (IsKeyDown(0x10) || IsKeyDown(0xA0) || IsKeyDown(0xA1)) mods |= ModShift; // Shift / LShift / RShift
            if (IsKeyDown(0x5B) || IsKeyDown(0x5C)) mods |= ModWin;                      // LWin / RWin
            if (IsKeyDown(0x20)) mods |= ModSpace;                                       // Space
            return mods;
        }

        private static uint ModFlagOf(uint vk)
        {
            return vk switch
            {
                (uint)Keys.ShiftKey or (uint)Keys.LShiftKey or (uint)Keys.RShiftKey => ModShift,
                (uint)Keys.ControlKey or (uint)Keys.LControlKey or (uint)Keys.RControlKey => ModCtrl,
                (uint)Keys.Menu or (uint)Keys.LMenu or (uint)Keys.RMenu => ModAlt,
                (uint)Keys.LWin or (uint)Keys.RWin => ModWin,
                (uint)Keys.Space => ModSpace,
                _ => 0
            };
        }

        private static void ResetCaptureModifiers()
        {
            _captureModsHeld = 0;
            _captureMultipleMods = false;
        }

        // Modifiers in effect for a given base key. When Space is the base key itself (e.g. Ctrl+Space)
        // it is not a modifier, so ModSpace is excluded in that case.
        private static uint GetModifiersFor(uint vkCode)
        {
            uint mods = GetCurrentModifiers();
            if ((vkCode & KeyMask) == (uint)Keys.Space) mods &= ~ModSpace;
            return mods;
        }

        private static uint ComposeCombo(uint vkCode)
        {
            return vkCode | GetModifiersFor(vkCode);
        }

        private static bool MatchesBinding(uint binding, uint vkCode, uint currentMods, bool exactOnly)
        {
            if ((binding & KeyMask) != vkCode) return false;
            uint mods = binding & ~KeyMask;
            if (mods == 0) return !exactOnly; // legacy plain key: fires regardless of held modifiers, only in the fallback pass
            // Non-Space modifiers must match exactly. Space is a "soft" modifier: it only blocks when the
            // binding explicitly requires it, so holding Space (e.g. jump) does not break other combos.
            uint required = mods & ~ModSpace;
            if (required != (currentMods & ~ModSpace)) return false;
            if ((mods & ModSpace) != 0 && (currentMods & ModSpace) == 0) return false;
            return true;
        }

        private bool TryFireSettingsAction(uint vkCode, uint currentMods, bool exactOnly)
        {
            if (MatchesBinding(_autoSelectKey, vkCode, currentMods, exactOnly))
            {
                TriggerAutoSelection();
                return true;
            }
            if (MatchesBinding(_reinforceKey, vkCode, currentMods, exactOnly))
            {
                TriggerStratagem(-1);
                return true;
            }
            foreach (var pair in _slotKey)
            {
                if (MatchesBinding(pair.Value, vkCode, currentMods, exactOnly))
                {
                    TriggerStratagem(pair.Key);
                    return true;
                }
            }
            return false;
        }

        private async Task<string?> MatchItemFromScreen(string targetType)
        {
            try
            {
                int rectX = 890;
                int rectY = 580;
                int rectW = 530;
                int rectH = 35;

                IntPtr hwnd = GetForegroundWindow();
                if (hwnd == IntPtr.Zero) return null;

                var className = new StringBuilder(256);
                GetClassName(hwnd, className, className.Capacity);

                if (className.ToString() != "stingray_window") return null;
                if (!GetClientRect(hwnd, out Rectangle clientRect)) return null;

                double currentAspect = (double)clientRect.Width / clientRect.Height;
                double targetAspect = 16.0 / 9.0;

                double finalRatio;
                double offsetX = 0;
                double offsetY = 0;

                if (currentAspect > targetAspect)
                {
                    finalRatio = (double)clientRect.Height / 1080.0;
                    offsetX = (clientRect.Width - (1920.0 * finalRatio)) / 2.0;
                }
                else
                {
                    finalRatio = (double)clientRect.Width / 1920.0;
                    offsetY = (clientRect.Height - (1080.0 * finalRatio)) / 2.0;
                }

                Point startPoint = new Point(0, 0);
                ClientToScreen(hwnd, ref startPoint);

                Rectangle region = new Rectangle(
                    startPoint.X + (int)Math.Round(rectX * finalRatio + offsetX),
                    startPoint.Y + (int)Math.Round(rectY * finalRatio + offsetY),
                    (int)Math.Round(rectW * finalRatio),
                    (int)Math.Round(rectH * finalRatio)
                );

                using (Bitmap cap = new Bitmap(region.Width, region.Height, PixelFormat.Format32bppArgb))
                {
                    using (Graphics g = Graphics.FromImage(cap))
                    {
                        g.CopyFromScreen(region.Left, region.Top, 0, 0, cap.Size);
                    }

                    double scale = 3.5;
                    double radius = 3.95;
                    int pad = 90;

                    int resizedW = (int)Math.Round(cap.Width * scale);
                    int resizedH = (int)Math.Round(cap.Height * scale);
                    int limit = (int)Math.Ceiling(radius);

                    using (Bitmap resized = new Bitmap(resizedW, resizedH, PixelFormat.Format32bppArgb))
                    {
                        using (Graphics rg = Graphics.FromImage(resized))
                        {
                            rg.InterpolationMode = InterpolationMode.HighQualityBicubic;
                            rg.DrawImage(cap, 0, 0, resized.Width, resized.Height);
                        }

                        var offsets = new List<(int dx, int dy)>();
                        for (int ky = -limit; ky <= limit; ky++)
                        {
                            for (int kx = -limit; kx <= limit; kx++)
                            {
                                if (Math.Sqrt(kx * kx + ky * ky) <= radius)
                                    offsets.Add((kx, ky));
                            }
                        }

                        int finalW = resized.Width + (pad * 2);
                        int finalH = resized.Height + (pad * 2);

                        BitmapData? srcData = null;
                        BitmapData? dstData = null;

                        using (Bitmap finalBmp = new Bitmap(finalW, finalH, PixelFormat.Format32bppArgb))
                        {
                            try
                            {
                                srcData = resized.LockBits(new Rectangle(0, 0, resized.Width, resized.Height), ImageLockMode.ReadOnly, PixelFormat.Format32bppArgb);
                                dstData = finalBmp.LockBits(new Rectangle(0, 0, finalW, finalH), ImageLockMode.WriteOnly, PixelFormat.Format32bppArgb);

                                int srcStride = Math.Abs(srcData.Stride);
                                int dstStride = Math.Abs(dstData.Stride);

                                byte[] srcPixels = new byte[srcStride * srcData.Height];
                                byte[] dstPixels = new byte[dstStride * dstData.Height];

                                Marshal.Copy(srcData.Scan0, srcPixels, 0, srcPixels.Length);
                                Array.Fill<byte>(dstPixels, 255);

                                for (int y = 0; y < resized.Height; y++)
                                {
                                    for (int x = 0; x < resized.Width; x++)
                                    {
                                        int srcIdx = (y * srcStride) + (x * 4);
                                        if (srcPixels[srcIdx + 0] > 165 && srcPixels[srcIdx + 1] > 165 && srcPixels[srcIdx + 2] > 165)
                                        {
                                            foreach (var (dx, dy) in offsets)
                                            {
                                                int outX = x + pad + dx;
                                                int outY = y + pad + dy;
                                                if (outX >= 0 && outX < finalW && outY >= 0 && outY < finalH)
                                                {
                                                    int dstIdx = (outY * dstStride) + (outX * 4);
                                                    dstPixels[dstIdx + 0] = 0;
                                                    dstPixels[dstIdx + 1] = 0;
                                                    dstPixels[dstIdx + 2] = 0;
                                                    dstPixels[dstIdx + 3] = 255;
                                                }
                                            }
                                        }
                                    }
                                }

                                Marshal.Copy(dstPixels, 0, dstData.Scan0, dstPixels.Length);
                            }
                            finally
                            {
                                if (srcData != null)
                                    resized.UnlockBits(srcData);

                                if (dstData != null)
                                    finalBmp.UnlockBits(dstData);
                            }

                            string rawText = "";
                            using (var ms = new MemoryStream())
                            {
                                finalBmp.Save(ms, ImageFormat.Png);
                                ms.Position = 0;

                                using var ras = ms.AsRandomAccessStream();
                                var decoder = await BitmapDecoder.CreateAsync(ras);

                                using (var softwareBitmap = await decoder.GetSoftwareBitmapAsync())
                                {
                                    if (_ocrEngine == null)
                                    {
                                        _ocrEngine = OcrEngine.TryCreateFromLanguage(new Windows.Globalization.Language("ko-KR"));
                                        if (_ocrEngine == null) return null;
                                    }

                                    var ocrResult = await _ocrEngine.RecognizeAsync(softwareBitmap);
                                    rawText = ocrResult.Text ?? "";
                                }
                            }

                            string Repair(string input) => input
                                .Replace(")(", "X").Replace("卜", "I").Replace("ⅹ", "X")
                                .Replace("ⅴ", "V").Replace("+", "B").Replace("l", "I")
                                .Replace("불", "블").Replace("뱸", "뱀").Replace("르", "드")
                                .Replace("엔", "맨").Replace("앤", "맨").Replace("멘", "맨")
                                .Replace("책", "잭").Replace("피", "퍼").Replace("저", "처")
                                .Replace("쳐", "처").Replace("적", "척").Replace("셀", "샐")
                                .Replace("일", "열").Replace("진", "친").Replace("제", "체")
                                .Replace("장", "창").Replace("04", "CM").Replace("21", "기")
                                .Replace("G-23", "23").Replace("I", "1").Replace("O", "0");

                            string Clean(string input) => Regex.Replace(input, @"[^가-힣a-zA-Z0-9]", "").ToUpper();

                            string cleanOCR = Clean(Repair(rawText));
                            if (string.IsNullOrEmpty(cleanOCR))
                            {
                                //Debug.WriteLine("[에러]: OCR이 텍스트를 추출하지 못했습니다.");
                                return null;
                            }

                            var matchResult = _parsedData
                                .Where(x => x.Type == targetType)
                                .Select(x => {
                                    string cleanDB = Clean(Repair(x.Name));
                                    int distance = GetLevenshteinDistance(cleanOCR, cleanDB);
                                    double sim = 1.0 - ((double)distance / Math.Max(cleanOCR.Length, cleanDB.Length));
                                    return new { Item = x, Similarity = sim };
                                })
                                .OrderByDescending(x => x.Similarity)
                                .FirstOrDefault();

                            /*
                            string folderPath = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "debug");
                            Directory.CreateDirectory(folderPath);
                            string debugPath = Path.Combine(folderPath, $"debug_{DateTime.Now:HHmmss}.png");
                            finalBmp.Save(debugPath, ImageFormat.Png);

                            string debugInfo = $"[OCR 인식 결과]: {rawText}\n" + $"[정제된 결과]: {cleanOCR}\n";
                            if (matchResult.Similarity != 1.0)
                            {
                                debugInfo += $"[가장 유사한 아이템]: {matchResult.Item.Name}\n" +
                                             $"[유사도]: {matchResult.Similarity:P1} (기준: 60%)\n" +
                                             $"[결과]: {(matchResult.Similarity > 0.6 ? "매칭 성공" : "매칭 실패 (유사도 낮음)")}";
                            }
                            else debugInfo = "유사도 완벽 일치";
                            Debug.WriteLine(debugInfo);
                            */

                            if (matchResult != null && matchResult.Similarity > 0.6)
                            {
                                return matchResult.Item.Name;
                            }
                            return null;
                        }
                    }
                }
            }
            catch
            {
                return null;
            }
        }

        private int GetLevenshteinDistance(string s, string t)
        {
            if (string.IsNullOrEmpty(s)) return string.IsNullOrEmpty(t) ? 0 : t.Length;
            if (string.IsNullOrEmpty(t)) return s.Length;
            int n = s.Length;
            int m = t.Length;
            int[,] d = new int[n + 1, m + 1];
            for (int i = 0; i <= n; d[i, 0] = i++) ;
            for (int j = 0; j <= m; d[0, j] = j++) ;
            for (int i = 1; i <= n; i++)
            {
                for (int j = 1; j <= m; j++)
                {
                    int cost = (t[j - 1] == s[i - 1]) ? 0 : 1;
                    d[i, j] = Math.Min(Math.Min(d[i - 1, j] + 1, d[i, j - 1] + 1), d[i - 1, j - 1] + cost);
                }
            }
            return d[n, m];
        }

        private void TriggerAutoSelection()
        {
            if (!IsGameActive() || _isChat)
                return;

            if (Interlocked.Exchange(ref _isSending, 1) == 1)
                return;

            Task.Run(async () =>
            {
                try
                {
                    //Debug.WriteLine(await MatchItemFromScreen("주 무기"));
                    await RunAutoSelection();
                }
                finally
                {
                    Interlocked.Exchange(ref _isSending, 0);
                }
            });
        }

        private async Task RunAutoSelection()
        {
            if (_currentLoadoutSlots.Any(s => !string.IsNullOrEmpty(s)))
            {
                await TapKey(Keys.R);
                await Task.Delay(250);

                int gearR = 0, gearC = 0;
                var gearLayout = new Dictionary<int, (int R, int C)>
                {
                    { 0, (0, 1) }, // 방어구
                    { 1, (1, 0) }, // 주 무기
                    { 2, (1, 1) }, // 보조 무기
                    { 3, (1, 2) }  // 투척 무기
                };

                for (int i = 0; i <= 3; i++)
                {
                    if (!string.IsNullOrEmpty(_currentLoadoutSlots[i]))
                    {
                        var targetSlot = gearLayout[i];

                        while (gearR < targetSlot.R) { await TapKey(Keys.S); gearR++; }
                        while (gearR > targetSlot.R) { await TapKey(Keys.W); gearR--; }

                        while (gearC < targetSlot.C) { await TapKey(Keys.D); gearC++; }
                        while (gearC > targetSlot.C) { await TapKey(Keys.A); gearC--; }

                        await TapKey(Keys.Space);
                        await ExecuteAutoSelection(i);

                        await TapKey(Keys.Escape);
                        await Task.Delay(250);
                    }
                }

                await TapKey(Keys.R);
                await Task.Delay(250);
            }

            if (_currentSlots.Where(name => !string.IsNullOrWhiteSpace(name))
                .Select(name => _parsedData.FirstOrDefault(d => d.Name == name))
                .Any(data => !string.IsNullOrEmpty(data.Name) && data.Category != "임무"))
            {
                await TapKey(Keys.Space);
                await ExecuteAutoSelection(4);
            }
        }

        private async Task ExecuteAutoSelection(int index)
        {
            async Task MoveToTarget((int Group, int Row, int Col) target, int curG, int curR, int curC, int totalTabs, int colCount, List<int> groupItemCounts)
            {
                while (curG != target.Group)
                {
                    int diff = target.Group - curG;
                    if (diff > totalTabs / 2 || (diff < 0 && diff >= -totalTabs / 2))
                    {
                        await TapKey(Keys.Z);
                        curG = (curG - 1 + totalTabs) % totalTabs;
                    }
                    else
                    {
                        await TapKey(Keys.C);
                        curG = (curG + 1) % totalTabs;
                    }
                    curR = 0;
                }

                await Task.Delay(250);

                while (curR != target.Row)
                {
                    int nextR = (curR < target.Row) ? curR + 1 : curR - 1;
                    if ((nextR * colCount) + curC >= groupItemCounts[curG])
                    {
                        curC = 0;
                    }

                    await TapKey(curR < target.Row ? Keys.S : Keys.W);
                    curR = nextR;
                }

                await Task.Delay(250);

                while (curC < target.Col) { await TapKey(Keys.D); curC++; }
                while (curC > target.Col) { await TapKey(Keys.A); curC--; }

                await TapKey(Keys.Space);
            }

            var (type, colCount) = index switch
            {
                0 => ("방어구", 3),
                1 => ("주 무기", 2),
                2 => ("보조 무기", 2),
                3 => ("투척 무기", 3),
                _ => ("스트라타젬", 4)
            };

            var groupedCategories = _parsedData
                .Where(d => d.Type == type && d.Category != "임무" && d.Category != "패시브" && !_disabledItems.Contains(d.Name))
                .GroupBy(d => d.Category)
                .ToList();

            var itemMap = new Dictionary<string, (int Group, int Row, int Col)>();
            var groupItemCounts = new List<int>();
            int totalTabs = groupedCategories.Count;

            for (int g = 0; g < totalTabs; g++)
            {
                var items = groupedCategories[g].ToList();

                int targetIndex = items.FindIndex(d => d.Name == "B-01 전술");
                if (targetIndex != -1)
                {
                    var original = items[targetIndex];
                    for (int j = 3; j >= 1; j--)
                    {
                        items.Insert(targetIndex + 1, (original.Type, original.Category, $"더미데이터{j}"));
                    }
                }

                groupItemCounts.Add(items.Count);

                for (int i = 0; i < items.Count; i++)
                {
                    itemMap[items[i].Name] = (g, i / colCount, i % colCount);
                }
            }

            int curG = 0, curR = 0, curC = 0;

            if (index >= 0 && index <= 3)
            {
                string? targetName = _currentLoadoutSlots[index];
                if (string.IsNullOrEmpty(targetName) || !itemMap.TryGetValue(targetName, out var target))
                    return;

                string? currentWeaponName = null;
                for (int retry = 0; retry < 3; retry++)
                {
                    currentWeaponName = await MatchItemFromScreen(type);
                    if (currentWeaponName != null) break;
                    await Task.Delay(150);
                }

                if (currentWeaponName != null && itemMap.TryGetValue(currentWeaponName, out var current))
                {
                    curG = current.Group;
                    curR = current.Row;
                    curC = current.Col;

                    await MoveToTarget(target, curG, curR, curC, totalTabs, colCount, groupItemCounts);
                }
            }
            else if (index == 4)
            {
                var selectedItems = _currentSlots
                     .Where(name => !string.IsNullOrWhiteSpace(name))
                     .Select(name => name!)
                     .Where(name => itemMap.ContainsKey(name))
                     .Where(name =>
                     {
                         var data = _parsedData.FirstOrDefault(d => d.Name == name);
                         return !string.IsNullOrEmpty(data.Name) && data.Category != "임무";
                     })
                     .Take(4)
                     .ToList();

                if (selectedItems.Count == 0)
                    return;

                foreach (var name in selectedItems)
                {
                    var target = itemMap[name];
                    await MoveToTarget(target, curG, curR, curC, totalTabs, colCount, groupItemCounts);

                    curG = target.Group;
                    curR = target.Row;
                    curC = target.Col;
                }
            }
        }

        private void TriggerStratagem(int slotIndex)
        {
            if (!IsGameActive() || _isChat)
                return;

            if (Interlocked.Exchange(ref _isSending, 1) == 1)
                return;

            string[]? seq = null;

            if (slotIndex == -1)
            {
                seq = new[] { "up", "down", "right", "left", "up" };
            }
            else
            {
                var slots = _currentSlots;

                if (slotIndex < 0 || slotIndex >= slots.Length)
                    return;

                string? name = slots[slotIndex];
                if (string.IsNullOrEmpty(name))
                    return;

                if (!_sequenceMap.TryGetValue(name, out seq) ||
                    seq == null || seq.Length == 0)
                    return;
            }

            Task.Run(() =>
            {
                try
                {
                    SendStratagem(seq);
                }
                finally
                {
                    Interlocked.Exchange(ref _isSending, 0);
                }
            });
        }

        private void SendStratagem(string[] seqArray)
        {
            if (!_stratagemKey.TryGetValue("start", out var startVk))
                return;

            var keySequence = new List<uint>();
            foreach (var dir in seqArray)
            {
                if (!_stratagemKey.TryGetValue(dir.ToLower(), out var vk))
                    return;
                keySequence.Add(vk);
            }

            try
            {
                switch (_stratagemType)
                {
                    case "Tap":
                    case "Press":
                        SendInput(startVk, true);
                        Thread.Sleep(_inputDelay);
                        SendInput(startVk, false);
                        break;

                    case "DoubleTap":
                        SendInput(startVk, true);
                        Thread.Sleep(_inputDelay);
                        SendInput(startVk, false);
                        Thread.Sleep(_inputDelay);
                        SendInput(startVk, true);
                        Thread.Sleep(_inputDelay);
                        SendInput(startVk, false);
                        break;

                    case "LongPress":
                        SendInput(startVk, true);
                        Thread.Sleep(300);
                        SendInput(startVk, false);
                        break;

                    case "Hold":
                        SendInput(startVk, true);
                        break;
                }

                Thread.Sleep(_inputDelay);

                foreach (var vk in keySequence)
                {
                    SendInput(vk, true);
                    Thread.Sleep(_inputDelay);
                    SendInput(vk, false);
                    Thread.Sleep(_inputDelay);
                }
            }
            finally
            {
                if (_stratagemType == "Hold")
                    SendInput(startVk, false);
            }
        }

        private void SendInput(uint vk, bool isDown)
        {
            uint flag = vk switch
            {
                0x01 => isDown ? 0x0002u : 0x0004u,
                0x02 => isDown ? 0x0008u : 0x0010u,
                0x04 => isDown ? 0x0020u : 0x0040u,
                0x05 or 0x06 => isDown ? 0x0080u : 0x0100u,
                _ => 0u
            };

            if (flag != 0) mouse_event(flag, 0, 0, vk >= 0x05 ? vk - 4u : 0u, IntPtr.Zero);
            else keybd_event((byte)vk, 0, isDown ? 0u : 2u, UIntPtr.Zero);
        }

        private async Task TapKey(Keys key)
        {
            SendInput((uint)key, true);
            await Task.Delay(_inputDelay);
            SendInput((uint)key, false);
            await Task.Delay(_inputDelay);
        }

        private uint? ParseInputKey(string? inputKey)
        {
            if (string.IsNullOrWhiteSpace(inputKey))
                return null;

            string enumKey = inputKey;

            switch (inputKey)
            {
                case "mousebuttonleft": enumKey = "LButton"; break;
                case "mousebuttonright": enumKey = "RButton"; break;
                case "mousebuttonmiddle": enumKey = "MButton"; break;
                case "mousebutton4": enumKey = "XButton1"; break;
                case "mousebutton5": enumKey = "XButton2"; break;

                case "backtick": enumKey = "Oemtilde"; break;
                case "minus": enumKey = "OemMinus"; break;
                case "equal": enumKey = "Oemplus"; break;
                case "open bracket": enumKey = "OemOpenBrackets"; break;
                case "close bracket": enumKey = "OemCloseBrackets"; break;
                case "backslash": enumKey = "OemPipe"; break;
                case "semicolon": enumKey = "OemSemicolon"; break;
                case "quote": enumKey = "OemQuotes"; break;
                case "comma": enumKey = "OemComma"; break;
                case "period": enumKey = "OemPeriod"; break;
                case "slash": enumKey = "OemQuestion"; break;
                case "backspace": enumKey = "Back"; break;

                case "left ctrl": enumKey = "LControlKey"; break;
                case "right ctrl": enumKey = "RControlKey"; break;
                case "left alt": enumKey = "LMenu"; break;
                case "right alt": enumKey = "RMenu"; break;
                case "left shift": enumKey = "LShiftKey"; break;
                case "right shift": enumKey = "RShiftKey"; break;
                case "kana": enumKey = "HangulMode"; break;
                case "kanji": enumKey = "HanjaMode"; break;
                case "caps lock": enumKey = "CapsLock"; break;
                case "page up": enumKey = "PageUp"; break;
                case "page down": enumKey = "PageDown"; break;

                case "numpad 0":
                case "numpad 1":
                case "numpad 2":
                case "numpad 3":
                case "numpad 4":
                case "numpad 5":
                case "numpad 6":
                case "numpad 7":
                case "numpad 8":
                case "numpad 9":
                    enumKey = "NumPad" + inputKey[^1];
                    break;

                case "numpad *": enumKey = "Multiply"; break;
                case "numpad +": enumKey = "Add"; break;
                case "numpad -": enumKey = "Subtract"; break;
                case "numpad .": enumKey = "Decimal"; break;
                case "numpad /": enumKey = "Divide"; break;
            }

            if (Enum.TryParse<Keys>(enumKey, true, out var parsedKey))
                return (uint)parsedKey;

            return null;
        }

        private string GetKeyName(uint value)
        {
            if (value == 0) return "없음";

            uint mods = value & ~KeyMask;
            if (mods == 0) return GetSingleKeyName(value);

            var parts = new List<string>();
            if ((mods & ModCtrl) != 0) parts.Add("Ctrl");
            if ((mods & ModAlt) != 0) parts.Add("Alt");
            if ((mods & ModShift) != 0) parts.Add("Shift");
            if ((mods & ModWin) != 0) parts.Add("Win");
            if ((mods & ModSpace) != 0) parts.Add("Space");
            parts.Add(GetSingleKeyName(value & KeyMask));
            return string.Join("+", parts);
        }

        private string GetSingleKeyName(uint value)
        {
            if (value >= 0x1001) return ((PadButton)value).ToString();

            var specialKeys = new Dictionary<Keys, string>
            {
                { Keys.LButton, "마우스 왼쪽" },
                { Keys.RButton, "마우스 오른쪽" },
                { Keys.MButton, "마우스 휠 클릭" },
                { Keys.XButton1, "마우스 버튼1" },
                { Keys.XButton2, "마우스 버튼2" },
                { Keys.Oemtilde, "` ~" },
                { Keys.OemMinus, "- _" },
                { Keys.Oemplus, "= +" },
                { Keys.OemOpenBrackets, "[ {" },
                { Keys.OemCloseBrackets, "] }" },
                { Keys.OemPipe, "\\ |" },
                { Keys.OemSemicolon, "; :" },
                { Keys.OemQuotes, "' \"" },
                { Keys.Oemcomma, ", <" },
                { Keys.OemPeriod, ". >" },
                { Keys.OemQuestion, "/ ?" },
                { Keys.Space, "Space" },
                { Keys.Return, "Enter" },
                { Keys.Back, "Backspace" },
                { Keys.ControlKey, "Ctrl" },
                { Keys.LControlKey, "LCtrl" },
                { Keys.RControlKey, "RCtrl" },
                { Keys.Menu, "Alt" },
                { Keys.LMenu, "LAlt" },
                { Keys.RMenu, "RAlt" },
                { Keys.ShiftKey, "Shift" },
                { Keys.LShiftKey, "LShift" },
                { Keys.RShiftKey, "RShift" },
                { Keys.LWin, "LWin" },
                { Keys.RWin, "RWin" },
                { Keys.HangulMode, "한/영" },
                { Keys.HanjaMode, "한자" },
                { Keys.CapsLock, "CapsLock" },
                { Keys.Escape, "ESC" },
                { Keys.Tab, "Tab" },
                { Keys.Delete, "Del" },
                { Keys.Insert, "Ins" },
                { Keys.Home, "Home" },
                { Keys.End, "End" },
                { Keys.PageUp, "PgUp" },
                { Keys.PageDown, "PgDn" },
                { Keys.Scroll, "Scroll" },
                { Keys.Pause, "Pause" },
                { Keys.Left, "←" },
                { Keys.Up, "↑" },
                { Keys.Right, "→" },
                { Keys.Down, "↓" },
                { Keys.NumPad0, "Num0" },
                { Keys.NumPad1, "Num1" },
                { Keys.NumPad2, "Num2" },
                { Keys.NumPad3, "Num3" },
                { Keys.NumPad4, "Num4" },
                { Keys.NumPad5, "Num5" },
                { Keys.NumPad6, "Num6" },
                { Keys.NumPad7, "Num7" },
                { Keys.NumPad8, "Num8" },
                { Keys.NumPad9, "Num9" },
                { Keys.NumLock, "NumLock" },
                { Keys.Multiply, "Num*" },
                { Keys.Add, "Num+" },
                { Keys.Subtract, "Num-" },
                { Keys.Decimal, "Num." },
                { Keys.Divide, "Num/" }
            };

            Keys k = (Keys)value;
            if (specialKeys.ContainsKey(k))
            {
                return specialKeys[k];
            }

            string name = k.ToString();
            if (name.Length == 2 && name.StartsWith("D") && char.IsDigit(name[1]))
            {
                return name.Substring(1);
            }

            return name;
        }

        private void OverlayShow()
        {
            if (!IsGameActive() || _isChat || CursorUtil.IsVisible())
                return;

            var slotNames = _currentSlots.Where(s => !string.IsNullOrEmpty(s)).ToArray();
            if (slotNames.Length == 0)
                return;

            var images = slotNames
                .Select(name => GetStratagemImage(name!))
                .ToArray();

            if (_overlayForm == null) _overlayForm = new OverlayForm(slotNames!, images!);
            else _overlayForm.UpdateSlot(slotNames!, images!);

            _overlayForm.Show();
        }

        private void OverlayHide()
        {
            if (_overlayForm != null)
            {
                string? selected = _overlayForm.Selected;

                _overlayForm.Hide();

                if (!string.IsNullOrEmpty(selected))
                {
                    Task.Run(async () =>
                    {
                        await Task.Delay(50);

                        int Index = Array.IndexOf(_currentSlots ?? Array.Empty<string>(), selected);
                        if (Index != -1)
                            TriggerStratagem(Index);
                    });
                }
            }
        }

        public class OverlayForm : Form
        {
            protected override bool ShowWithoutActivation => true;

            private const int BaseOverlaySize = 515;
            private const float BasePlacementRadius = 163.75f;
            private const float BaseDeadZoneRadius = 70f;
            private const float BaseLargeIconSize = 256f / 3f;
            private const float BaseSmallIconSize = 256f / 4f;
            private const float BaseMouseMultiplier = 1.8f;

            private readonly float overlayScale;
            private readonly int overlaySize;
            private readonly float placementRadius;
            private readonly float deadZoneRadius;
            private readonly float mouseMultiplier;
            private readonly float cursorRadius;

            private CancellationTokenSource? loopCts;
            private bool isUpdating = false;
            private int selectedSlot = -1;

            private string[] slotNames;
            private string[] lastNames;
            private int slotCount;
            private Image[] slotImages;
            private float iconSize;

            private Bitmap[]? selectionBuffers;
            private Bitmap staticBuffer;
            private Bitmap backBuffer;
            private readonly Graphics staticBufferGraphics;
            private readonly Graphics backBufferGraphics;

            private IntPtr hBitmap;
            private IntPtr pBits;
            private IntPtr memDC;
            private IntPtr oldBitmap;

            private readonly int centerX, centerY;
            private float virtualX, virtualY;
            private Point currentMousePos;
            private Point lastRawPos;

            private readonly SolidBrush evenBrush = new SolidBrush(Color.FromArgb(153, 0x15, 0x15, 0x15));
            private readonly SolidBrush oddBrush = new SolidBrush(Color.FromArgb(153, 0x33, 0x33, 0x33));
            private readonly SolidBrush lastBrush = new SolidBrush(Color.FromArgb(153, 0x22, 0x22, 0x22));
            private readonly SolidBrush selectionBrush = new SolidBrush(Color.FromArgb(153, 180, 180, 180));
            private readonly Font textFont;
            private readonly Pen linePen;

            public string? Selected
            {
                get
                {
                    if (slotNames != null && selectedSlot >= 0 && selectedSlot < slotNames.Length)
                        return slotNames[selectedSlot];
                    return null;
                }
            }

            public OverlayForm(string[] names, Image[] images)
            {
                Load += OverlayForm_Load;

                var screen = Screen.PrimaryScreen!.Bounds;
                int screenCenterX = screen.Width / 2;
                int screenCenterY = screen.Height / 2;

                overlayScale = (float)Math.Min((double)screen.Width / BaseReferenceWidth, (double)screen.Height / BaseReferenceHeight); 
                overlaySize = Math.Max(1, (int)Math.Round(BaseOverlaySize * overlayScale));
                placementRadius = BasePlacementRadius * overlayScale;
                deadZoneRadius = BaseDeadZoneRadius * overlayScale;
                mouseMultiplier = BaseMouseMultiplier * overlayScale;
                cursorRadius = 7f * overlayScale;

                FormBorderStyle = FormBorderStyle.None;
                StartPosition = FormStartPosition.Manual;
                TopMost = true;
                ShowInTaskbar = false;
                Width = overlaySize;
                Height = overlaySize;
                Left = screenCenterX - Width / 2;
                Top = screenCenterY - Height / 2;

                slotNames = names;
                lastNames = names;
                slotCount = slotNames.Length;
                slotImages = images;
                iconSize = (slotCount > 8 ? BaseSmallIconSize : BaseLargeIconSize) * overlayScale;

                centerX = overlaySize / 2;
                centerY = overlaySize / 2;
                currentMousePos = new Point(centerX, centerY);
                virtualX = centerX;
                virtualY = centerY;

                using (Graphics g = this.CreateGraphics()) { textFont = new Font("Malgun Gothic", 12 / (g.DpiX / 96.0f), FontStyle.Bold); }
                linePen = new Pen(Color.White, Math.Max(1f, 3f * overlayScale)) { StartCap = LineCap.Round, EndCap = LineCap.Round };

                staticBuffer = new Bitmap(overlaySize, overlaySize, PixelFormat.Format32bppPArgb);
                staticBufferGraphics = Graphics.FromImage(staticBuffer);
                staticBufferGraphics.SmoothingMode = SmoothingMode.AntiAlias;
                staticBufferGraphics.TextRenderingHint = System.Drawing.Text.TextRenderingHint.ClearTypeGridFit;
                staticBufferGraphics.InterpolationMode = InterpolationMode.HighQualityBicubic;
                staticBufferGraphics.PixelOffsetMode = PixelOffsetMode.HighQuality;

                IntPtr screenDC = GetDC(IntPtr.Zero);
                memDC = CreateCompatibleDC(screenDC);

                BITMAPINFO bmi = new BITMAPINFO();
                bmi.biSize = Marshal.SizeOf(typeof(BITMAPINFO));
                bmi.biWidth = overlaySize;
                bmi.biHeight = -overlaySize;
                bmi.biPlanes = 1;
                bmi.biBitCount = 32;
                bmi.biCompression = 0;

                hBitmap = CreateDIBSection(memDC, ref bmi, 0, out pBits, IntPtr.Zero, 0);
                oldBitmap = SelectObject(memDC, hBitmap);

                backBuffer = new Bitmap(overlaySize, overlaySize, overlaySize * 4, PixelFormat.Format32bppPArgb, pBits);
                backBufferGraphics = Graphics.FromImage(backBuffer);
                backBufferGraphics.SmoothingMode = SmoothingMode.AntiAlias;
                backBufferGraphics.TextRenderingHint = System.Drawing.Text.TextRenderingHint.ClearTypeGridFit;
                backBufferGraphics.InterpolationMode = InterpolationMode.HighQualityBicubic;
                backBufferGraphics.PixelOffsetMode = PixelOffsetMode.HighQuality;

                ReleaseDC(IntPtr.Zero, screenDC);
            }

            private void OverlayForm_Load(object? sender, EventArgs e)
            {
                int exStyle = GetWindowLong(Handle, GWL_EXSTYLE);
                SetWindowLong(Handle, GWL_EXSTYLE, exStyle | WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TRANSPARENT | WS_EX_TOOLWINDOW);

                RenderStaticBackground();
                RenderOverlay();
            }

            protected override void OnVisibleChanged(EventArgs e)
            {
                base.OnVisibleChanged(e);

                if (this.Visible) StartLoop();
                else StopLoop();
            }

            private void StartLoop()
            {
                StopLoop();

                lastRawPos = Cursor.Position;
                loopCts = new CancellationTokenSource();
                var token = loopCts.Token;

                Task.Run(async () =>
                {
                    while (!token.IsCancellationRequested)
                    {
                        if (_isChat || CursorUtil.IsVisible())
                        {
                            this.BeginInvoke(new Action(() => this.Hide()));
                            break;
                        }

                        Point currentRawPos = Cursor.Position;
                        int dx = currentRawPos.X - lastRawPos.X;
                        int dy = currentRawPos.Y - lastRawPos.Y;

                        if (Math.Abs(dx) < 100 && Math.Abs(dy) < 100 && (dx != 0 || dy != 0))
                        {
                            UpdateVirtualMouse(dx, dy);

                            if (!isUpdating)
                            {
                                isUpdating = true;
                                this.BeginInvoke(new Action(() =>
                                {
                                    try
                                    {
                                        if (this.IsDisposed || !this.Visible) return;
                                        UpdateSelectionFromPos((int)virtualX, (int)virtualY);
                                    }
                                    finally
                                    {
                                        isUpdating = false;
                                    }
                                }));
                            }
                        }

                        lastRawPos = currentRawPos;
                        await Task.Delay(16, token);
                    }
                }, token);
            }

            private void StopLoop()
            {
                loopCts?.Cancel();
                loopCts?.Dispose();
                loopCts = null;
            }

            public void UpdateSlot(string[] names, Image[] images)
            {
                slotNames = names;
                slotCount = names.Length;
                slotImages = images;
                iconSize = (slotCount > 8 ? BaseSmallIconSize : BaseLargeIconSize) * overlayScale;

                currentMousePos = new Point(centerX, centerY);
                virtualX = centerX;
                virtualY = centerY;
                selectedSlot = -1;

                if (!lastNames.SequenceEqual(names))
                {
                    lastNames = names;
                    RenderStaticBackground();
                }

                RenderOverlay();
            }

            private void UpdateVirtualMouse(int dx, int dy)
            {
                virtualX += dx * mouseMultiplier;
                virtualY += dy * mouseMultiplier;

                float vDx = virtualX - centerX;
                float vDy = virtualY - centerY;
                double distSq = vDx * vDx + vDy * vDy;

                if (distSq > placementRadius * placementRadius)
                {
                    float dist = (float)Math.Sqrt(distSq);
                    virtualX = centerX + (vDx / dist) * placementRadius;
                    virtualY = centerY + (vDy / dist) * placementRadius;
                }
            }

            private void UpdateSelectionFromPos(int x, int y)
            {
                float dx = x - centerX;
                float dy = y - centerY;
                float distanceSq = dx * dx + dy * dy;
                int newSelectedSlot = -1;

                if (slotCount > 0 && distanceSq > deadZoneRadius * deadZoneRadius)
                {
                    const double TAU = Math.PI * 2.0;
                    double angle = Math.Atan2(dy, dx) + (Math.PI / 2.0) + (TAU / (slotCount * 2.0));
                    angle = (angle % TAU + TAU) % TAU;
                    newSelectedSlot = (int)(angle / (TAU / slotCount)) % slotCount;
                }

                selectedSlot = newSelectedSlot;
                currentMousePos = new Point(x, y);

                RenderOverlay();
            }

            private void RenderStaticBackground()
            {
                var g = staticBufferGraphics;
                g.Clear(Color.Transparent);

                using (GraphicsPath outerPath = new GraphicsPath())
                using (GraphicsPath innerPath = new GraphicsPath())
                {
                    outerPath.AddEllipse(0, 0, overlaySize, overlaySize);
                    innerPath.AddEllipse(centerX - deadZoneRadius, centerY - deadZoneRadius, deadZoneRadius * 2, deadZoneRadius * 2);

                    using (Region donutRegion = new Region(outerPath))
                    {
                        donutRegion.Exclude(innerPath);
                        g.Clip = donutRegion;

                        float sectorAngle = 360f / slotCount;
                        float startAngle = -90f - (sectorAngle / 2f);

                        if (selectionBuffers != null)
                            foreach (var bmp in selectionBuffers) bmp?.Dispose();
                        selectionBuffers = new Bitmap[slotCount];

                        for (int i = 0; i < slotCount; i++)
                        {
                            float currentStartAngle = startAngle + (sectorAngle * i);

                            var sectorBrush = (slotCount % 2 == 1 && i == slotCount - 1) ? lastBrush : (i % 2 == 0 ? evenBrush : oddBrush);
                            g.FillPie(sectorBrush, 0, 0, overlaySize, overlaySize, currentStartAngle, sectorAngle);

                            var bmp = new Bitmap(overlaySize, overlaySize, PixelFormat.Format32bppPArgb);
                            using (var sg = Graphics.FromImage(bmp))
                            {
                                sg.SmoothingMode = SmoothingMode.AntiAlias;
                                sg.PixelOffsetMode = PixelOffsetMode.HighQuality;
                                sg.CompositingMode = CompositingMode.SourceCopy;
                                sg.Clip = donutRegion;
                                sg.FillPie(selectionBrush, 0, 0, overlaySize, overlaySize, currentStartAngle, sectorAngle);
                            }
                            selectionBuffers[i] = bmp;
                        }
                    }
                }

                g.ResetClip();

                double sectorAngleRad = (Math.PI * 2.0) / slotCount;
                double startAngleRad = -Math.PI / 2.0 - (sectorAngleRad / 2.0);

                for (int i = 0; i < slotCount; i++)
                {
                    double currentIconRad = startAngleRad + (sectorAngleRad * i) + (sectorAngleRad / 2.0);
                    float x = centerX + (float)(placementRadius * Math.Cos(currentIconRad)) - iconSize / 2;
                    float y = centerY + (float)(placementRadius * Math.Sin(currentIconRad)) - iconSize / 2;

                    if (slotImages[i] != null)
                        g.DrawImage(slotImages[i], x, y, iconSize, iconSize);
                    else if (!string.IsNullOrEmpty(slotNames[i]))
                    {
                        SizeF textSize = g.MeasureString(slotNames[i], textFont);
                        g.DrawString(slotNames[i], textFont, Brushes.White,
                            x + (iconSize - textSize.Width) / 2,
                            y + (iconSize - textSize.Height) / 2);
                    }
                }
            }

            private void RenderOverlay()
            {
                var g = backBufferGraphics;

                g.CompositingMode = CompositingMode.SourceCopy;
                g.DrawImageUnscaled(staticBuffer, 0, 0);
                g.CompositingMode = CompositingMode.SourceOver;

                if (selectionBuffers != null && selectedSlot >= 0 && selectedSlot < slotCount)
                    g.DrawImageUnscaled(selectionBuffers[selectedSlot], 0, 0);

                g.DrawLine(linePen, centerX, centerY, currentMousePos.X, currentMousePos.Y);

                g.FillEllipse(Brushes.White,
                    currentMousePos.X - cursorRadius,
                    currentMousePos.Y - cursorRadius,
                    cursorRadius * 2, cursorRadius * 2);

                ApplyLayeredWindow();
            }

            private void ApplyLayeredWindow()
            {
                IntPtr screenDC = GetDC(IntPtr.Zero);

                try
                {
                    SIZE size = new SIZE(overlaySize, overlaySize);
                    POINT pointSource = new POINT(0, 0);
                    POINT topPos = new POINT(this.Left, this.Top);

                    BLENDFUNCTION blend = new BLENDFUNCTION
                    {
                        BlendOp = AC_SRC_OVER,
                        BlendFlags = 0,
                        SourceConstantAlpha = 255,
                        AlphaFormat = AC_SRC_ALPHA
                    };

                    UpdateLayeredWindow(Handle, screenDC, ref topPos, ref size, memDC, ref pointSource, 0, ref blend, ULW_ALPHA);
                }
                finally
                {
                    ReleaseDC(IntPtr.Zero, screenDC);
                }
            }

            protected override void Dispose(bool disposing)
            {
                if (disposing)
                {
                    StopLoop();

                    staticBufferGraphics?.Dispose();
                    staticBuffer?.Dispose();
                    backBufferGraphics?.Dispose();
                    backBuffer?.Dispose();

                    if (oldBitmap != IntPtr.Zero) SelectObject(memDC, oldBitmap);
                    if (hBitmap != IntPtr.Zero) DeleteObject(hBitmap);
                    if (memDC != IntPtr.Zero) DeleteDC(memDC);

                    evenBrush?.Dispose();
                    oddBrush?.Dispose();
                    lastBrush?.Dispose();
                    selectionBrush?.Dispose();
                    textFont?.Dispose();
                    linePen?.Dispose();

                    if (selectionBuffers != null)
                        foreach (var bmp in selectionBuffers) bmp?.Dispose();
                }
                base.Dispose(disposing);
            }

            #region WinAPI
            private const int WS_EX_TRANSPARENT = 0x00000020;
            private const int WS_EX_LAYERED = 0x00080000;
            private const int WS_EX_NOACTIVATE = 0x08000000;
            private const int WS_EX_TOOLWINDOW = 0x00000080;
            private const int GWL_EXSTYLE = -20;
            private const byte AC_SRC_OVER = 0x00;
            private const int ULW_ALPHA = 0x02;
            private const byte AC_SRC_ALPHA = 0x01;

            [StructLayout(LayoutKind.Sequential)]
            private struct POINT { public int X, Y; public POINT(int x, int y) { X = x; Y = y; } }

            [StructLayout(LayoutKind.Sequential)]
            private struct SIZE { public int cx, cy; public SIZE(int x, int y) { cx = x; cy = y; } }

            [StructLayout(LayoutKind.Sequential, Pack = 1)]
            private struct BLENDFUNCTION
            {
                public byte BlendOp, BlendFlags, SourceConstantAlpha, AlphaFormat;
            }

            [StructLayout(LayoutKind.Sequential)]
            private struct BITMAPINFO
            {
                public int biSize;
                public int biWidth;
                public int biHeight;
                public short biPlanes;
                public short biBitCount;
                public int biCompression;
                public int biSizeImage;
                public int biXPelsPerMeter;
                public int biYPelsPerMeter;
                public int biClrUsed;
                public int biClrImportant;
            }

            [DllImport("user32.dll", SetLastError = true)]
            private static extern bool UpdateLayeredWindow(IntPtr hwnd, IntPtr hdcDst, ref POINT pptDst, ref SIZE psize,
                IntPtr hdcSrc, ref POINT pptSrc, int crKey, ref BLENDFUNCTION pblend, int dwFlags);

            [DllImport("gdi32.dll", SetLastError = true)]
            private static extern IntPtr CreateDIBSection(IntPtr hdc, ref BITMAPINFO pbmi, uint iUsage, out IntPtr ppvBits, IntPtr hSection, uint dwOffset);

            [DllImport("user32.dll", SetLastError = true)]
            private static extern IntPtr GetDC(IntPtr hWnd);

            [DllImport("user32.dll", SetLastError = true)]
            private static extern int ReleaseDC(IntPtr hWnd, IntPtr hDC);

            [DllImport("gdi32.dll", SetLastError = true)]
            private static extern IntPtr CreateCompatibleDC(IntPtr hDC);

            [DllImport("gdi32.dll", SetLastError = true)]
            private static extern bool DeleteDC(IntPtr hdc);

            [DllImport("gdi32.dll", SetLastError = true)]
            private static extern IntPtr SelectObject(IntPtr hdc, IntPtr hObject);

            [DllImport("gdi32.dll", SetLastError = true)]
            private static extern bool DeleteObject(IntPtr hObject);

            [DllImport("user32.dll", SetLastError = true)]
            private static extern int GetWindowLong(IntPtr hWnd, int nIndex);

            [DllImport("user32.dll", SetLastError = true)]
            private static extern int SetWindowLong(IntPtr hWnd, int nIndex, int dwNewLong);
            #endregion
        }

        public static class GamepadReader
        {
            private const string MappingUrl = "https://raw.githubusercontent.com/mdqinc/SDL_GameControllerDB/master/gamecontrollerdb.txt";
            private static IntPtr activeController = IntPtr.Zero;
            private static readonly Dictionary<int, IntPtr> connectedPads = new();
            private static HashSet<PadButton> lastButtons = new(), currentButtonsSet = new();
            private static float rightX, rightY;

            public class PadEvent
            {
                public PadButton Button;
                public bool Pressed;
            }

            public static async Task InitializeAsync()
            {
                SDL.SDL_SetHint("SDL_GAMECONTROLLER_ALLOW_BACKGROUND_EVENTS", "1");
                SDL.SDL_SetHint("SDL_GAMECONTROLLER_IGNORE_DEVICES", "");
                SDL.SDL_Init(SDL.SDL_INIT_GAMECONTROLLER | SDL.SDL_INIT_JOYSTICK | SDL.SDL_INIT_VIDEO);

                try
                {
                    using var client = new HttpClient { Timeout = TimeSpan.FromSeconds(2) };
                    string db = await client.GetStringAsync(MappingUrl);
                    var lines = db.Split(new[] { '\n', '\r' }, StringSplitOptions.RemoveEmptyEntries);

                    foreach (var line in lines)
                    {
                        if (!line.StartsWith("#") && !string.IsNullOrWhiteSpace(line))
                            SDL.SDL_GameControllerAddMapping(line);
                    }

                    for (int i = 0; i < SDL.SDL_NumJoysticks(); i++)
                    {
                        ForceRefreshController(i);
                    }
                }
                catch { }
            }

            private static void UpdateCurrentButtons()
            {
                currentButtonsSet.Clear();

                while (SDL.SDL_PollEvent(out var ev) != 0)
                {
                    switch (ev.type)
                    {
                        case SDL.SDL_EventType.SDL_CONTROLLERDEVICEADDED:
                            ForceRefreshController(ev.cdevice.which);
                            break;
                        case SDL.SDL_EventType.SDL_CONTROLLERDEVICEREMOVED:
                            RemoveController(ev.cdevice.which);
                            break;
                    }
                }

                foreach (var entry in connectedPads)
                {
                    IntPtr pad = entry.Value;
                    for (byte i = 0; i < (byte)SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_MAX; i++)
                    {
                        if (SDL.SDL_GameControllerGetButton(pad, (SDL.SDL_GameControllerButton)i) == 1)
                        {
                            activeController = pad;
                            break;
                        }
                    }
                }

                if (activeController == IntPtr.Zero) return;

                void Map(SDL.SDL_GameControllerButton s, PadButton p)
                {
                    if (SDL.SDL_GameControllerGetButton(activeController, s) == 1) currentButtonsSet.Add(p);
                }

                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_A, PadButton.PadA);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_B, PadButton.PadB);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_X, PadButton.PadX);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_Y, PadButton.PadY);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_LEFTSHOULDER, PadButton.L1);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_RIGHTSHOULDER, PadButton.R1);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_LEFTSTICK, PadButton.L3);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_RIGHTSTICK, PadButton.R3);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_START, PadButton.PadStart);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_BACK, PadButton.PadBack);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_DPAD_UP, PadButton.DUp);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_DPAD_DOWN, PadButton.DDown);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_DPAD_LEFT, PadButton.DLeft);
                Map(SDL.SDL_GameControllerButton.SDL_CONTROLLER_BUTTON_DPAD_RIGHT, PadButton.DRight);

                if (SDL.SDL_GameControllerGetAxis(activeController, SDL.SDL_GameControllerAxis.SDL_CONTROLLER_AXIS_TRIGGERLEFT) > 8000) currentButtonsSet.Add(PadButton.L2);
                if (SDL.SDL_GameControllerGetAxis(activeController, SDL.SDL_GameControllerAxis.SDL_CONTROLLER_AXIS_TRIGGERRIGHT) > 8000) currentButtonsSet.Add(PadButton.R2);

                rightX = SDL.SDL_GameControllerGetAxis(activeController, SDL.SDL_GameControllerAxis.SDL_CONTROLLER_AXIS_RIGHTX) / 32767f;
                rightY = SDL.SDL_GameControllerGetAxis(activeController, SDL.SDL_GameControllerAxis.SDL_CONTROLLER_AXIS_RIGHTY) / 32767f;
            }

            private static void ForceRefreshController(int index)
            {
                if (SDL.SDL_IsGameController(index) == SDL.SDL_bool.SDL_TRUE)
                {
                    IntPtr tempPad = SDL.SDL_GameControllerOpen(index);
                    if (tempPad == IntPtr.Zero) return;

                    int instanceId = SDL.SDL_JoystickInstanceID(SDL.SDL_GameControllerGetJoystick(tempPad));

                    if (connectedPads.TryGetValue(instanceId, out IntPtr existing))
                    {
                        if (activeController == existing) activeController = IntPtr.Zero;
                        SDL.SDL_GameControllerClose(existing);
                        connectedPads.Remove(instanceId);
                    }
                    else
                    {
                        SDL.SDL_GameControllerClose(tempPad);
                    }

                    IntPtr finalPad = SDL.SDL_GameControllerOpen(index);
                    if (finalPad != IntPtr.Zero)
                    {
                        connectedPads[instanceId] = finalPad;
                        if (activeController == IntPtr.Zero) activeController = finalPad;
                    }

                    _isChat = false;
                    _isPad = true;
                }
            }

            private static void RemoveController(int instanceId)
            {
                if (connectedPads.TryGetValue(instanceId, out IntPtr pad))
                {
                    if (activeController == pad) activeController = IntPtr.Zero;
                    SDL.SDL_GameControllerClose(pad);
                    connectedPads.Remove(instanceId);
                    if (activeController == IntPtr.Zero && connectedPads.Count > 0)
                        activeController = connectedPads.Values.First();
                }
            }

            public static List<PadEvent> GetButtonEvents()
            {
                var events = new List<PadEvent>();
                UpdateCurrentButtons();

                foreach (var btn in currentButtonsSet)
                    if (!lastButtons.Contains(btn)) events.Add(new PadEvent { Button = btn, Pressed = true });
                foreach (var btn in lastButtons)
                    if (!currentButtonsSet.Contains(btn)) events.Add(new PadEvent { Button = btn, Pressed = false });

                lastButtons = new HashSet<PadButton>(currentButtonsSet);
                return events;
            }

            public static (float dx, float dy) GetRightStick()
            {
                const float dz = 0.2f;
                float Filter(float v) => Math.Abs(v) < dz ? 0 : (v - (dz * Math.Sign(v))) / (1f - dz);
                return (Filter(rightX), Filter(rightY));
            }

            public static void Quit()
            {
                foreach (var pad in connectedPads.Values) SDL.SDL_GameControllerClose(pad);
                connectedPads.Clear();
                SDL.SDL_Quit();
            }
        }

        public class HangulEngine
        {
            private static readonly string CHOSUNG = "ㄱㄲㄴㄷㄸㄹㅁㅂㅃㅅㅆㅇㅈㅉㅊㅋㅌㅍㅎ";
            private static readonly string JUNGSUNG = "ㅏㅐㅑㅒㅓㅔㅕㅖㅗㅘㅙㅚㅛㅜㅝㅞㅟㅠㅡㅢㅣ";
            private static readonly string JONGSUNG = " ㄱㄲㄳㄴㄵㄶㄷㄹㄺㄻㄼㄽㄾㄿㅀㅁㅂㅄㅅㅆㅇㅈㅊㅋㅌㅍㅎ";

            private static readonly Dictionary<string, char> COMPLEX_VOWELS = new()
            {
                {"ㅗㅏ", 'ㅘ'}, {"ㅗㅐ", 'ㅙ'}, {"ㅗㅣ", 'ㅚ'},
                {"ㅜㅓ", 'ㅝ'}, {"ㅜㅔ", 'ㅞ'}, {"ㅜㅣ", 'ㅟ'}, {"ㅡㅣ", 'ㅢ'}
            };

            private static readonly Dictionary<string, char> COMPLEX_JONGS = new()
            {
                {"ㄱㅅ", 'ㄳ'}, {"ㄴㅈ", 'ㄵ'}, {"ㄴㅎ", 'ㄶ'}, {"ㄹㄱ", 'ㄺ'},
                {"ㄹㅁ", 'ㄻ'}, {"ㄹㅂ", 'ㄼ'}, {"ㄹㅅ", 'ㄽ'}, {"ㄹㅌ", 'ㄾ'},
                {"ㄹㅍ", 'ㄿ'}, {"ㄹㅎ", 'ㅀ'}, {"ㅂㅅ", 'ㅄ'}
            };

            private static readonly Dictionary<string, char> KOR_MAP = new()
            {
                { "r", 'ㄱ' }, { "s", 'ㄴ' }, { "e", 'ㄷ' }, { "f", 'ㄹ' },
                { "a", 'ㅁ' }, { "q", 'ㅂ' }, { "t", 'ㅅ' }, { "d", 'ㅇ' },
                { "w", 'ㅈ' }, { "c", 'ㅊ' }, { "z", 'ㅋ' }, { "x", 'ㅌ' },
                { "v", 'ㅍ' }, { "g", 'ㅎ' }, { "k", 'ㅏ' }, { "o", 'ㅐ' },
                { "i", 'ㅑ' }, { "j", 'ㅓ' }, { "p", 'ㅔ' }, { "u", 'ㅕ' },
                { "h", 'ㅗ' }, { "y", 'ㅛ' }, { "n", 'ㅜ' }, { "b", 'ㅠ' },
                { "m", 'ㅡ' }, { "l", 'ㅣ' }
            };

            private List<char> history = new();
            private string fixedText = "";

            public bool ProcessInput(uint vkCode, bool isShift)
            {
                string k = ((Keys)vkCode).ToString().ToLower();
                char jamo = '\0';

                if (isShift)
                {
                    jamo = k switch
                    {
                        "r" => 'ㄲ',
                        "e" => 'ㄸ',
                        "q" => 'ㅃ',
                        "t" => 'ㅆ',
                        "w" => 'ㅉ',
                        "o" => 'ㅒ',
                        "p" => 'ㅖ',
                        _ => '\0'
                    };
                }

                if (jamo == '\0') KOR_MAP.TryGetValue(k, out jamo);
                if (jamo == '\0') return false;

                Add(jamo);
                return true;
            }

            public void Add(char jamo)
            {
                history.Add(jamo);

                string composed = Compose(history);

                if (composed.Length >= 2)
                {
                    int removeCount = FindRemoveCount(composed);
                    if (removeCount > 0)
                    {
                        fixedText += composed[0];
                        history.RemoveRange(0, removeCount);
                    }
                }
            }

            private int FindRemoveCount(string composed)
            {
                int limit = Math.Min(history.Count, 6);
                for (int i = 1; i <= limit; i++)
                {
                    if (Compose(history.Skip(i).ToList()) == composed.Substring(1))
                        return i;
                }
                return 0;
            }

            public void Backspace()
            {
                if (history.Count > 0)
                {
                    history.RemoveAt(history.Count - 1);
                }
                else if (fixedText.Length > 0)
                {
                    fixedText = fixedText.Substring(0, fixedText.Length - 1);
                }
            }

            public void Flush()
            {
                fixedText += Compose(history);
                history.Clear();
            }

            public void Clear()
            {
                history.Clear();
                fixedText = "";
            }

            public string GetCurrentText() => fixedText + Compose(history);

            public bool IsComposing() => history.Count > 0;

            private string Compose(List<char> input)
            {
                if (input.Count == 0) return "";

                StringBuilder result = new StringBuilder();
                int cho = -1, jung = -1, jong = 0;

                foreach (var c in input)
                {
                    int cCho = CHOSUNG.IndexOf(c);
                    int cJung = JUNGSUNG.IndexOf(c);

                    if (cJung != -1)
                    {
                        ProcessVowel(c, cJung, ref cho, ref jung, ref jong, result);
                    }
                    else if (cCho != -1)
                    {
                        ProcessConsonant(c, cCho, ref cho, ref jung, ref jong, result);
                    }
                    else
                    {
                        if (cho != -1) result.Append(Assemble(cho, jung, jong));
                        result.Append(c);
                        cho = -1; jung = -1; jong = 0;
                    }
                }

                if (cho != -1)
                {
                    if (jung != -1) result.Append(Assemble(cho, jung, jong));
                    else result.Append(CHOSUNG[cho]);
                }

                return result.ToString();
            }

            private void ProcessVowel(char c, int cJung, ref int cho, ref int jung, ref int jong, StringBuilder result)
            {
                if (cho != -1 && jung == -1)
                {
                    jung = cJung;
                    return;
                }

                if (cho != -1 && jung != -1 && jong == 0)
                {
                    if (COMPLEX_VOWELS.TryGetValue($"{JUNGSUNG[jung]}{c}", out char v))
                    {
                        jung = JUNGSUNG.IndexOf(v);
                    }
                    else
                    {
                        result.Append(Assemble(cho, jung, 0));
                        cho = -1; jung = cJung;
                    }
                    return;
                }

                if (cho != -1 && jung != -1 && jong != 0)
                {
                    HandleDokkaebibull(cJung, ref cho, ref jung, ref jong, result);
                    return;
                }

                if (cho != -1) result.Append(Assemble(cho, jung, jong));
                result.Append(c);
                cho = -1; jung = -1; jong = 0;
            }

            private void HandleDokkaebibull(int cJung, ref int cho, ref int jung, ref int jong, StringBuilder result)
            {
                string jongStr = JONGSUNG[jong].ToString();
                var complexPair = COMPLEX_JONGS.FirstOrDefault(p => p.Value.ToString() == jongStr);

                if (!complexPair.Equals(default(KeyValuePair<string, char>)))
                {
                    result.Append(Assemble(cho, jung, JONGSUNG.IndexOf(complexPair.Key[0].ToString())));
                    cho = CHOSUNG.IndexOf(complexPair.Key[1]);
                }
                else
                {
                    result.Append(Assemble(cho, jung, 0));
                    cho = CHOSUNG.IndexOf(JONGSUNG[jong]);
                }
                jung = cJung;
                jong = 0;
            }

            private void ProcessConsonant(char c, int cCho, ref int cho, ref int jung, ref int jong, StringBuilder result)
            {
                if (cho == -1)
                {
                    cho = cCho;
                }
                else if (jung == -1)
                {
                    result.Append(CHOSUNG[cho]);
                    cho = cCho;
                }
                else if (jong == 0)
                {
                    int j = JONGSUNG.IndexOf(c.ToString());
                    if (j != -1) jong = j;
                    else { result.Append(Assemble(cho, jung, 0)); cho = cCho; jung = -1; }
                }
                else
                {
                    if (COMPLEX_JONGS.TryGetValue($"{JONGSUNG[jong]}{c}", out char j))
                    {
                        jong = JONGSUNG.IndexOf(j.ToString());
                    }
                    else
                    {
                        result.Append(Assemble(cho, jung, jong));
                        cho = cCho; jung = -1; jong = 0;
                    }
                }
            }

            private char Assemble(int cho, int jung, int jong)
            {
                return (char)(0xAC00 + (cho * 21 * 28) + (jung * 28) + jong);
            }
        }

        public class InputHookManager : IDisposable
        {
            private const int WH_KEYBOARD_LL = 13;
            private const int WH_MOUSE_LL = 14;

            public event EventHandler<InputEventArgs>? OnInputEvent;
            private readonly Dictionary<uint, bool> keyStates = new();
            private static readonly Dictionary<uint, long> lastTicks = new();

            private IntPtr keyboardHook = IntPtr.Zero;
            private IntPtr mouseHook = IntPtr.Zero;
            private delegate IntPtr LowLevelKeyboardProc(int nCode, IntPtr wParam, IntPtr lParam);
            private delegate IntPtr LowLevelMouseProc(int nCode, IntPtr wParam, IntPtr lParam);
            private readonly LowLevelKeyboardProc keyboardProc;
            private readonly LowLevelMouseProc mouseProc;
      
            private HangulEngine engine = new();
            private string lastInjected = "";
            private bool isHangulMode = true;
            private bool isProcessing = false;

            public InputHookManager()
            {
                keyboardProc = KeyboardHookCallback;
                mouseProc = MouseHookCallback;
                keyboardHook = SetWindowsHookEx(WH_KEYBOARD_LL, keyboardProc, IntPtr.Zero, 0);
                mouseHook = SetWindowsHookEx(WH_MOUSE_LL, mouseProc, IntPtr.Zero, 0);
            }

            private IntPtr KeyboardHookCallback(int nCode, IntPtr wParam, IntPtr lParam)
            {
                if (nCode >= 0 && !isProcessing)
                {
                    uint vkCode = (uint)Marshal.ReadInt32(lParam);
                    bool isDown = (wParam == (IntPtr)0x0100 || wParam == (IntPtr)0x0104);

                    if (IsGameActive() && !_isPad)
                    {
                        if (isDown)
                        {
                            if (vkCode == (uint)Keys.HangulMode)
                            {
                                if (_isChat) isHangulMode = !isHangulMode;

                                if (!isHangulMode && engine.IsComposing())
                                {
                                    engine.Flush();
                                    ExecuteInjectDiff(lastInjected, engine.GetCurrentText());
                                    ResetHangulState();
                                }

                                return (IntPtr)1;
                            }

                            if (vkCode == _chatKey)
                            {
                                foreach (var mouse in _mouseKey)
                                {
                                    if ((GetAsyncKeyState((int)mouse.Key) & 0x8000) != 0)
                                    {
                                        if (mouse.Value.Trigger.Contains("Hold"))
                                        {
                                            return CallNextHookEx(keyboardHook, nCode, wParam, lParam);
                                        }
                                        else if (mouse.Value.Trigger.Contains("LongPress"))
                                        {
                                            if (lastTicks.TryGetValue(mouse.Key, out long t) && t != 0)
                                            {
                                                if ((Environment.TickCount64 - t) >= mouse.Value.Threshold)
                                                {
                                                    _isChat = false;
                                                    ResetHangulState();
                                                    lastTicks[mouse.Key] = 0;
                                                }
                                            }
                                        }
                                    }
                                }

                                if (_chatKey == (uint)Keys.Enter) _isChat = !_isChat;
                                else _isChat = true;
                            }
                            else if (vkCode == (uint)Keys.Escape || vkCode == (uint)Keys.Enter)
                            {
                                _isChat = false;
                            }
                        }

                        if (_isChat)
                        {
                            isProcessing = true;
                            bool handled = ProcessHangulBypass(vkCode, isDown);
                            isProcessing = false;
                            if (handled) return (IntPtr)1;
                        }
                        else
                        {
                            ResetHangulState();
                        }
                    }

                    if (HasStateChanged(vkCode, isDown))
                    {
                        OnInputEvent?.Invoke(this, new InputEventArgs(vkCode, isDown));
                    }
                }
                return CallNextHookEx(keyboardHook, nCode, wParam, lParam);
            }

            private IntPtr MouseHookCallback(int nCode, IntPtr wParam, IntPtr lParam)
            {
                if (nCode >= 0)
                {
                    uint vk = wParam switch
                    {
                        (IntPtr)0x0201 or (IntPtr)0x0202 => 0x01u,
                        (IntPtr)0x0204 or (IntPtr)0x0205 => 0x02u,
                        (IntPtr)0x0207 or (IntPtr)0x0208 => 0x04u,
                        (IntPtr)0x020B or (IntPtr)0x020C => (uint)((Marshal.ReadInt32(lParam, 8) >> 16) == 1 ? 0x05 : 0x06),
                        _ => 0u
                    };

                    if (vk != 0)
                    {
                        bool isDown = (wParam == (IntPtr)0x0201 || wParam == (IntPtr)0x0204 || wParam == (IntPtr)0x0207 || wParam == (IntPtr)0x020B);

                        if (IsGameActive() && _isChat)
                        {
                            if (vk == 0x02u || _mouseKey.ContainsKey(vk))
                            {
                                if (!_mouseKey.TryGetValue(vk, out var action) && vk == 0x02u)
                                {
                                    action = ("Press", 0);
                                }

                                if (action.Trigger != null)
                                {
                                    bool shouldClose = false;

                                    if (action.Trigger.Contains("Hold"))
                                    {
                                        shouldClose = true;
                                    }
                                    else if (action.Trigger == "LongPress")
                                    {
                                        if (vk == 0x02u)
                                        {
                                            shouldClose = true;
                                        }
                                        else if (isDown)
                                        {
                                            lastTicks[vk] = Environment.TickCount64;
                                        }
                                        else
                                        {
                                            if (lastTicks.TryGetValue(vk, out long t) && t != 0)
                                            {
                                                if ((Environment.TickCount64 - t) >= action.Threshold)
                                                {
                                                    shouldClose = true;
                                                }
                                            }
                                            lastTicks[vk] = 0;
                                        }
                                    }
                                    else if (action.Trigger == "DoubleTap")
                                    {
                                        if (vk == 0x02u)
                                        {
                                            shouldClose = true;
                                        }
                                        else if (isDown)
                                        {
                                            long currentTick = Environment.TickCount64;
                                            if (lastTicks.TryGetValue(vk, out long t) && t != 0 && (currentTick - t) < action.Threshold)
                                            {
                                                shouldClose = true;
                                                lastTicks[vk] = 0;
                                            }
                                        }
                                        else
                                        {
                                            lastTicks[vk] = Environment.TickCount64;
                                        }
                                    }
                                    else
                                    {
                                        shouldClose = (action.Trigger == "Release") ? !isDown : isDown;
                                    }

                                    if (shouldClose)
                                    {
                                        _isChat = false;
                                        ResetHangulState();
                                    }
                                }
                            }
                        }

                        if (HasStateChanged(vk, isDown))
                        {
                            OnInputEvent?.Invoke(this, new InputEventArgs(vk, isDown));
                        }
                    }
                }
                return CallNextHookEx(mouseHook, nCode, wParam, lParam);
            }

            private bool HasStateChanged(uint vkCode, bool isDown)
            {
                lock (keyStates)
                {
                    if (keyStates.TryGetValue(vkCode, out bool currentState))
                    {
                        if (currentState == isDown) return false;
                    }
                    keyStates[vkCode] = isDown;
                    return true;
                }
            }

            private bool ProcessHangulBypass(uint vkCode, bool isDown)
            {
                if (vkCode >= 0x10 && vkCode <= 0x12 || vkCode == 0x09)
                    return false;

                if (!isHangulMode)
                    return false;

                bool isAlphabet = (vkCode >= 0x41 && vkCode <= 0x5A);
                bool isBack = (vkCode == (uint)Keys.Back);

                if (!isAlphabet && !isBack)
                {
                    if (isDown && engine.IsComposing())
                    {
                        engine.Flush();
                        ExecuteInjectDiff(lastInjected, engine.GetCurrentText());
                        ResetHangulState();
                    }
                    return false;
                }

                if (!isDown)
                    return engine.IsComposing();

                if (isBack)
                {
                    if (!engine.IsComposing() && lastInjected.Length == 0) return false;
                    engine.Backspace();
                }
                else
                {
                    bool isShift = false;
                    lock (keyStates)
                    {
                        isShift = (keyStates.TryGetValue(16, out bool s) && s) ||
                            (keyStates.TryGetValue(160, out bool ls) && ls) ||
                            (keyStates.TryGetValue(161, out bool rs) && rs);
                    }

                    if (!engine.ProcessInput(vkCode, isShift))
                    {
                        engine.Flush();
                        ResetHangulState();
                        return false;
                    }
                }

                string nextText = engine.GetCurrentText();
                ExecuteInjectDiff(lastInjected, nextText);
                lastInjected = nextText;

                return true;
            }

            private void ExecuteInjectDiff(string prev, string curr)
            {
                if (prev == curr) return;

                int common = 0;
                int minLength = Math.Min(prev.Length, curr.Length);
                while (common < minLength && prev[common] == curr[common])
                {
                    common++;
                }

                int bsCount = prev.Length - common;

                if (bsCount > 0)
                {
                    INPUT[] bsInputs = new INPUT[bsCount * 2];
                    for (int i = 0; i < bsCount; i++)
                    {
                        bsInputs[i * 2] = CreateInput((ushort)Keys.Back, 0x0E, 0);
                        bsInputs[i * 2 + 1] = CreateInput((ushort)Keys.Back, 0x0E, 0x0002);
                    }

                    SendInput((uint)bsInputs.Length, bsInputs, Marshal.SizeOf(typeof(INPUT)));
                    Thread.Sleep(30);
                }

                if (common < curr.Length)
                {
                    string toAdd = curr.Substring(common);
                    INPUT[] inInputs = new INPUT[toAdd.Length * 2];
                    for (int i = 0; i < toAdd.Length; i++)
                    {
                        inInputs[i * 2] = CreateInput(0, (ushort)toAdd[i], 0x0004);
                        inInputs[i * 2 + 1] = CreateInput(0, (ushort)toAdd[i], 0x0004 | 0x0002);
                    }

                    SendInput((uint)inInputs.Length, inInputs, Marshal.SizeOf(typeof(INPUT)));
                    Thread.Sleep(2);
                }
            }

            private void ResetHangulState()
            {
                engine.Clear();
                lastInjected = "";
            }

            private INPUT CreateInput(ushort vk, ushort scan, uint flags)
            {
                INPUT input = new INPUT { type = 1 };
                input.ki.wVk = vk;
                input.ki.wScan = scan;
                input.ki.dwFlags = flags;
                input.ki.time = 0;
                input.ki.dwExtraInfo = IntPtr.Zero;
                return input;
            }

            public void Dispose()
            {
                if (keyboardHook != IntPtr.Zero)
                    UnhookWindowsHookEx(keyboardHook);

                if (mouseHook != IntPtr.Zero)
                    UnhookWindowsHookEx(mouseHook);
            }

            #region WinAPI
            [DllImport("user32.dll", SetLastError = true)]
            private static extern IntPtr SetWindowsHookEx(int idHook, Delegate lpfn, IntPtr hMod, uint dwThreadId);

            [DllImport("user32.dll")]
            private static extern bool UnhookWindowsHookEx(IntPtr hhk);

            [DllImport("user32.dll")]
            private static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);

            [DllImport("user32.dll", SetLastError = true)]
            private static extern uint SendInput(uint nInputs, INPUT[] pInputs, int cbSize);

            [DllImport("user32.dll")]
            private static extern short GetAsyncKeyState(int vKey);

            [StructLayout(LayoutKind.Explicit, Size = 40)]
            private struct INPUT
            {
                [FieldOffset(0)] public uint type;
                [FieldOffset(8)] public KEYBDINPUT ki;
            }

            [StructLayout(LayoutKind.Sequential)]
            private struct KEYBDINPUT
            {
                public ushort wVk;
                public ushort wScan;
                public uint dwFlags;
                public uint time;
                public IntPtr dwExtraInfo;
            }
            #endregion
        }

        public static class CursorUtil
        {
            [StructLayout(LayoutKind.Sequential)]
            private struct CURSORINFO
            {
                public int cbSize;
                public int flags;
                public IntPtr hCursor;
                public Point ptScreenPos;
            }

            [DllImport("user32.dll")]
            private static extern bool GetCursorInfo(out CURSORINFO pci);

            public static bool IsVisible()
            {
                CURSORINFO ci = new CURSORINFO();
                ci.cbSize = Marshal.SizeOf(ci);

                if (GetCursorInfo(out ci))
                {
                    return (ci.flags & 0x00000001) != 0;
                }

                return false;
            }
        }

        public static class Logger
        {
            private static readonly string logFile =
                    Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "log.txt");

            private static readonly object locker = new();

            public static void Log(string msg)
            {
                string line = $"[{DateTime.Now:HH:mm:ss.fff}] {msg}";

                lock (locker)
                {
                    File.AppendAllText(logFile, line + Environment.NewLine);
                }
            }
        }

        protected override void OnFormClosed(FormClosedEventArgs e)
        {
            _inputHook?.Dispose();
            _padLoopCts?.Cancel();
            _padLoopCts?.Dispose();
            _overlayForm?.Dispose();
            _webView?.Dispose();

            GamepadReader.Quit();

            _webView = null;
            _overlayForm = null;
            _padLoopCts = null;
            _inputHook = null;

            _parsedData.Clear();
            _sequenceMap.Clear();

            foreach (var img in _imageCache.Values) img?.Dispose();
            _imageCache.Clear();

            base.OnFormClosed(e);
            Environment.Exit(0);
        }
    }
}
