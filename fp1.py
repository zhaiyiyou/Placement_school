import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog, simpledialog
import random
import requests
import os
import time
import shutil
import subprocess
from tqdm import tqdm
import threading
import sys
import webbrowser
from PIL import Image, ImageTk
import io
import pystray
from pystray import MenuItem as item
from PIL import Image as PILImage
from plyer import notification
import cv2
import pyaudio

def is_camera_in_use():
    try:
        cap = cv2.VideoCapture(0, cv2.CAP_DSHOW)
        if not cap or not cap.isOpened():
            cap2 = cv2.VideoCapture(0, cv2.CAP_MSMF)
            if not cap2 or not cap2.isOpened():
                return True
            ret = cap2.read()[0]
            cap2.release()
            return not ret
        ret = cap.read()[0]
        cap.release()
        return not ret
    except Exception:
        return True

def is_microphone_in_use():
    p = None
    stream = None
    try:
        p = pyaudio.PyAudio()
        device_index = None
        for i in range(p.get_device_count()):
            info = p.get_device_info_by_index(i)
            if info.get('maxInputChannels', 0) > 0:
                device_index = i
                break
        if device_index is None:
            return False # 没有输入设备，所以不存在被占用的情况
        stream = p.open(format=pyaudio.paInt16, channels=1, rate=16000, input=True, input_device_index=device_index, frames_per_buffer=1024)
        stream.read(1024, exception_on_overflow=True) # 尝试读取，如果缓冲区溢出则抛出异常，表明可能被占用
        return False
    except Exception:
        return True
    finally:
        try:
            if stream is not None:
                stream.stop_stream()
                stream.close()
        except Exception:
            pass
        try:
            if p is not None:
                p.terminate()
        except Exception:
            pass

# 新增：默认密码（可修改）
NORMAL_PASSWORD = "$!Qs1225"
SPECIAL_PASSWORD = "$!Kight1225"
GUEST_PASSWORD = "1234567"
# 新增：默认备用密码（仅在联网获取失败时使用）
BUILTIN_NORMAL_PASSWORD = "$!Qs1225"
BUILTIN_SPECIAL_PASSWORD = "$!Kight1225"
PASSWORD_SERVER = "http://47.108.28.79/file/222"  # password.txt 将位于此地址下

def fetch_passwords(timeout=6):
    """
    尝试从服务器获取 password.txt，期望内容为两行：
    第一行为普通密码，第二行为特殊密码。
    返回 (normal_pwd, special_pwd, fetch_failed_bool, error_message_or_None)
    """
    try:
        url = f"{PASSWORD_SERVER}/password.txt"
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115.0.0.0 Safari/537.36',
            'Accept': 'text/plain',
            'Connection': 'close'
        }
        resp = requests.get(url, headers=headers, timeout=timeout)
        resp.raise_for_status()
        text = resp.text.strip().splitlines()
        if len(text) >= 2:
            normal = text[0].strip()
            special = text[1].strip()
            if normal == "" or special == "":
                raise ValueError("服务器返回的密码为空")
            return normal, special, False, None
        else:
            raise ValueError("服务器返回的 password.txt 格式不正确（需两行）")
    except Exception as e:
        # 返回备用密码并标记为获取失败，同时返回错误信息
        return BUILTIN_NORMAL_PASSWORD, BUILTIN_SPECIAL_PASSWORD, True, str(e)

class SeatAllocatorGUI:
    def __init__(self, root, correct_rules_enabled=False, export_mode=False):
        self.root = root
        self.root.title("Hyper Seats Randomer OS v6.2.0 你猜更新了个啥")
        self.root.geometry("1020x600")
        self.root.minsize(800, 600)
        
        # 不使用深色背景，仅使用背景图片（图片可包含透明通道）
        try:
            # 确保窗口整体不被额外透明化（图片本身保留 alpha）
            self.root.attributes("-alpha", 3.0)
        except Exception:
            pass

        # 背景图片（联网获取、仅内存使用，不写磁盘）
        # 图片路径：从 update_server 的 /picture.png 获取（可改为其它 URL）
        self._bg_url = f"http://47.108.28.79/file/222/picture.png"
        # 背景容器，先创建占位，后续在主线程设置 image
        self._bg_label = tk.Label(self.root, bg="#000000")
        self._bg_label.place(x=0, y=0, relwidth=1, relheight=1)
        self._original_bg_image = None
        self._bg_img = None  # 保持 PhotoImage 引用，防止被回收
        # 启动后台线程获取图片（不阻塞 UI）
        threading.Thread(target=self._fetch_and_apply_bg, daemon=True).start()
        # 在窗口尺寸改变时重新应用已获取的图片
        self.root.bind("<Configure>", lambda e: self._on_root_resize(e))
        
        # 版本信息
        self.version = "6.0.0"
        self.ans = [[" "] * 7 for _ in range(8)]  # 8行7列的初始化
        self.array1 = []
        self.array2 = []
        self.rules = []  # 规则相关功能已禁用，但保留变量以免出错
        self.downloading = False
        self.updating = False
        # 新增：规则修正功能开关状态（由启动密码决定）
        self.correct_rules_enabled = correct_rules_enabled
        # 兼容旧代码：一些地方使用 special_mode，等同于 correct_rules_enabled
        self.special_mode = correct_rules_enabled
        # 记录导出权限（访客密码会将其设为 False）
        self.export_mode = export_mode
        self.visitor_mode = not export_mode
        
        # 应用程序文件名
        self.app_filename = os.path.basename(sys.argv[0])
        # 更新服务器地址
        self.update_server = "http://47.108.28.79/file/222"
        
        # 创建样式，控件背景改为使用窗口当前背景，避免覆盖背景图片
        self.style = ttk.Style()
        # 普通按钮：黑色字体（按钮背景保持默认或可自定义）
        self.style.configure("TButton", font=("微软雅黑", 10), foreground="#000000")
        # 标签/标题使用窗口背景以便背景图透出
        win_bg = self.root.cget("bg")
        self.style.configure("TLabel", font=("微软雅黑", 10), background=win_bg)
        self.style.configure("Header.TLabel", font=("微软雅黑", 14, "bold"), background=win_bg)
        # 更新按钮：黑色字体（保留醒目背景）
        self.style.configure("Update.TButton", font=("微软雅黑", 10), foreground="#000000", background="#AF5656")
        # 框架与分组使用窗口背景，避免深色块遮挡图片
        self.style.configure("TFrame", background=win_bg)
        self.style.configure("TLabelframe", background=win_bg)
        self.style.configure("TLabelframe.Label", background=win_bg)

        self._create_widgets()
        # 根据启动时密码设置规则修正状态显示
        #try:
        #    if self.correct_rules_enabled:
        #        self.rules_status_label.config(text="规则修正: 已启用", foreground="#7CFC00")
        #    else:
        #        self.rules_status_label.config(text="规则修正: 已禁用", foreground="#aaaaaa")
        #except Exception:
        #    pass
        
        # 绑定Ctrl+I快捷键切换规则修正功能（已禁用）
        # self.root.bind("<Control-i>", self.toggle_correct_rules)
    
    def _create_widgets(self):
        # 顶部标题和版本信息
        header_frame = ttk.Frame(self.root, padding=10)
        header_frame.pack(fill=tk.X, padx=20, pady=10)
        
        title_frame = ttk.Frame(header_frame)
        title_frame.pack(side=tk.LEFT)
        
        ttk.Label(
            title_frame, 
            text="Hyper Seats Randomer OS v6.0.0 Safty Update", 
            style="Header.TLabel"
        ).pack(side=tk.LEFT)
        
        ttk.Label(
            title_frame, 
            text=f"v{self.version}", 
            font=("微软雅黑", 10)
        ).pack(side=tk.LEFT, padx=10)
        
        # 显示规则修正功能状态的标签（显示为已禁用）
        #self.rules_status_label = ttk.Label(
        #    title_frame, 
        #    text="规则修正: 已禁用", 
        #    font=("微软雅黑", 10),
        #    foreground="#aaaaaa"  # 灰色表示禁用
        #)
        #self.rules_status_label.pack(side=tk.LEFT, padx=20)
        
        # 检查更新按钮 - 应用Update.TButton样式
        self.check_update_btn = ttk.Button(
            header_frame, 
            text="检查更新", 
            command=self.check_for_updates,
            style="Update.TButton"  # 添加此行以应用更新按钮样式
        )
        self.check_update_btn.pack(side=tk.RIGHT)
        
        # 其余界面元素创建代码与原代码一致...
        # 主内容区
        main_frame = ttk.Frame(self.root, padding=10)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
        
        # 左侧控制面板
        control_frame = ttk.LabelFrame(main_frame, text="控制中心", padding=10)
        control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        # 下载控制
        ttk.Label(control_frame, text="名单管理:").pack(anchor=tk.W, pady=(10, 5))
        
        self.download_btn = ttk.Button(
            control_frame, 
            text="获取/更新名单", 
            command=self._handle_download
        )
        self.download_btn.pack(fill=tk.X, pady=5)
        
        # 生成控制
        ttk.Label(control_frame, text="座位生成:").pack(anchor=tk.W, pady=(20, 5))
        
        self.generate_btn = ttk.Button(
            control_frame, 
            text="生成座位表", 
            command=self._generate_seats,
            state=tk.DISABLED
        )
        self.generate_btn.pack(fill=tk.X, pady=5)
        
        # 导出控制
        ttk.Label(control_frame, text="结果导出:").pack(anchor=tk.W, pady=(20, 5))
        export_state = tk.NORMAL if getattr(self, "export_mode", True) else tk.DISABLED
        self.export_btn = ttk.Button(
            control_frame, 
            text="导出座位表", 
            command=self._export_seats,
            state=export_state
        )
        self.export_btn.pack(fill=tk.X, pady=5)
        # 访客专用：打开访客页面（从 page.txt 在线读取），仅在访客模式显示
        if getattr(self, "visitor_mode", False):
            self.guest_page_btn = ttk.Button(
                control_frame,
                text="千万别点",
                command=self._open_guest_page
            )
            self.guest_page_btn.pack(fill=tk.X, pady=(8,5))
        
        # 状态显示
        ttk.Label(control_frame, text="系统状态:").pack(anchor=tk.W, pady=(20, 5))
        
        self.status_var = tk.StringVar(value="等待操作...")
        ttk.Label(
            control_frame, 
            textvariable=self.status_var, 
            foreground="#4ecdc4"
        ).pack(anchor=tk.W, pady=5)
        
        # 座位表显示区域
        seat_frame = ttk.LabelFrame(main_frame, text="座位表预览", padding=10)
        seat_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        self.seat_canvas = tk.Canvas(seat_frame, bg="#3d3d3d", highlightthickness=0)
        self.seat_scroll_x = ttk.Scrollbar(seat_frame, orient=tk.HORIZONTAL, command=self.seat_canvas.xview)
        self.seat_scroll_y = ttk.Scrollbar(seat_frame, orient=tk.VERTICAL, command=self.seat_canvas.yview)
        self.seat_frame_inner = ttk.Frame(self.seat_canvas, style="TFrame")
        
        self.seat_frame_inner.bind(
            "<Configure>",
            lambda e: self.seat_canvas.configure(
                scrollregion=self.seat_canvas.bbox("all")
            )
        )
        
        self.seat_canvas.create_window((0, 0), window=self.seat_frame_inner, anchor="nw")
        self.seat_canvas.configure(xscrollcommand=self.seat_scroll_x.set, yscrollcommand=self.seat_scroll_y.set)
        
        self.seat_scroll_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.seat_scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.seat_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # 初始化座位表显示
        self._init_seat_display()
        
        # 日志区域
        log_frame = ttk.LabelFrame(self.root, text="操作日志", padding=10)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=(5, 20))
        
        self.log_text = scrolledtext.ScrolledText(
            log_frame, 
            wrap=tk.WORD, 
            font=("微软雅黑", 9),
            height=10,
            insertbackground="white",
            highlightthickness=0
        )
        self.log_text.pack(fill=tk.BOTH, expand=True)
        self.log_text.config(state=tk.DISABLED)
        
        # 检查是否已有文件
        self._check_existing_files()
        
        # 如果是访客模式（没有导出权限），确保导出按钮被禁用
        if not getattr(self, "export_mode", True):
            try:
                self.export_btn.config(state=tk.DISABLED)
                # 在日志中记录访客模式（仅记录，不弹窗）
                self._log("访客模式：导出功能已禁用")
            except Exception:
                pass
        

        # 启动时自动检查更新
        self.root.after(2000, self.check_for_updates, False)
        self._setup_tray_icon() # 初始化系统托盘图标
        self._setup_tray_icon() # 初始化系统托盘图标
    
    def toggle_correct_rules(self, event=None):
        """切换规则修正功能的启用状态（已禁用）"""
        # 该功能已被注释/禁用，保留空实现以防外部引用
        #self._log("规则修正功能已被禁用")
        return
    
    def _init_seat_display(self):
        # 创建座位格子
        for r in range(8):  # 行
            for c in range(7):  # 列
                frame = ttk.Frame(
                    self.seat_frame_inner,
                    width=100,
                    height=60,
                    relief=tk.SOLID,
                    borderwidth=1,
                    style="TFrame"
                )
                frame.grid(row=r, column=c, padx=2, pady=2)
                frame.grid_propagate(False)
                
                label = tk.Label(
                    frame,
                    text="",
                    font=("微软雅黑", 10),
                    wraplength=90,
                    bg=self.root.cget("bg"),  # 继承窗口背景（图片）
                )
                label.place(relx=0.5, rely=0.5, anchor=tk.CENTER)
                
                # 存储引用
                setattr(self, f"seat_{r}_{c}", label)
                
        # 标记区域
        area_label = ttk.Label(
            self.seat_frame_inner,
            text="中间区域",
            font=("微软雅黑", 10, "bold"),
            background="#4a69bd",
            foreground="#ffffff"
        )
        area_label.grid(row=2, column=7, padx=5, pady=2, rowspan=4, sticky="ns")
        
        area_label = ttk.Label(
            self.seat_frame_inner,
            text="靠墙区域",
            font=("微软雅黑", 10, "bold"),
            background="#60a3bc",
            foreground="#ffffff"
        )
        area_label.grid(row=0, column=7, padx=5, pady=2, rowspan=2, sticky="ns")
        area_label = ttk.Label(
            self.seat_frame_inner,
            text="靠墙区域",
            font=("微软雅黑", 10, "bold"),
            background="#60a3bc",
            foreground="#ffffff"
        )
        area_label.grid(row=6, column=7, padx=5, pady=2, rowspan=2, sticky="ns")
    
    def _update_seat_display(self):
        # 修正行列遍历顺序，确保与UI一致
        for r in range(8):  # 行
            for c in range(7):  # 列
                seat_label = getattr(self, f"seat_{r}_{c}")
                seat_label.config(text=self.ans[r][c])
                
                # 根据区域设置背景色（深色主题适配）
                if 2 <= r <= 5:  # 中间区域
                    seat_label.configure(background="#4a69bd", foreground="#ffffff")
                else:  # 靠墙区域
                    seat_label.configure(background="#60a3bc", foreground="#ffffff")
        
        # 仅当有导出权限时启用导出按钮（访客模式保持禁用）
        if getattr(self, "export_mode", True):
            self.export_btn.config(state=tk.NORMAL)
        else:
            self.export_btn.config(state=tk.DISABLED)
    
    def _log(self, message):
        """添加日志信息"""
        self.log_text.config(state=tk.NORMAL)
        self.log_text.insert(tk.END, f"[{time.strftime('%H:%M:%S')}] {message}\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)
    
    def _open_guest_page(self):
        def worker():
            try:
                # 获取page.txt内容
                url_text = self._fetch_text(f"{self.update_server}/page.txt", timeout=10)
                # 取第一行非空作为URL
                url = None
                for line in url_text.splitlines():
                    line = line.strip()
                    if line:
                        url = line
                        break
                if not url:
                    raise ValueError("page.txt 内容为空或无可用 URL")
                # 打开默认浏览器
                webbrowser.open(url)  # 核心打开浏览器的代码
            except Exception as e:
                # 错误弹窗（需在主线程执行）
                self.root.after(0, lambda: messagebox.showerror("错误", f"无法打开访客页面: {e}"))
            finally:
                # 恢复按钮状态（需在主线程执行）
                self.root.after(0, lambda: self.guest_page_btn.config(state=tk.NORMAL))
    
        # 修正：在worker函数外部启动线程
        self.guest_page_btn.config(state=tk.DISABLED)  # 点击后禁用按钮，避免重复操作
        threading.Thread(target=worker, daemon=True).start()

    def _fetch_and_apply_bg(self):
        """从服务器获取背景图片并应用到窗口"""
        try:
            # 获取图片数据
            response = requests.get(self._bg_url, timeout=10)
            response.raise_for_status()
            
            # 使用PIL处理图片
            image_data = io.BytesIO(response.content)
            pil_image = Image.open(image_data)
            
            # 保存原始图片用于后续调整大小
            self._original_bg_image = pil_image
            
            # 调整图片大小以适应窗口
            window_width = self.root.winfo_width()
            window_height = self.root.winfo_height()
            if window_width < 100:  # 如果窗口还没显示，使用默认大小
                window_width, window_height = 900, 700
            
            resized_image = pil_image.resize((window_width, window_height), Image.Resampling.LANCZOS)
            tk_image = ImageTk.PhotoImage(resized_image)
            
            # 在主线程中设置背景
            self.root.after(0, lambda: self._apply_background_image(tk_image))
            
        except Exception as e:
            # 如果加载失败，记录日志但继续运行
            self.root.after(0, lambda: self._log(f"背景图片加载失败: {e}"))
    
    def _apply_background_image(self, tk_image):
        """应用背景图片到窗口"""
        # 保存图片引用，防止被垃圾回收
        self._fg_img = tk_image
        
        # 设置背景图片
        self._bg_label.config(image=tk_image)
        self._bg_label.lower()  # 确保背景在最顶层
    
    def _on_root_resize(self, event):
        """窗口大小改变时重新调整背景图片大小"""
        if self._original_bg_image is None:  # 如果背景图片未初始化，直接返回
            return
        
        if event.widget == self.root:
            # 获取新的窗口尺寸
            new_width = event.width
            new_height = event.height
            
            # 调整图片大小
            resized_image = self._original_bg_image.resize((new_width, new_height), Image.Resampling.LANCZOS)
            tk_image = ImageTk.PhotoImage(resized_image)
            
            # 应用新的背景图片
            self._apply_background_image(tk_image)

    def _check_existing_files(self):
        """检查是否已有必要文件"""
        required_files = ["students.txt", "rules.txt"]
        all_exists = all(os.path.exists(f) for f in required_files)
        
        if all_exists:
            self._log("检测到已有数据文件")
            self.generate_btn.config(state=tk.NORMAL)
            # 尝试加载数据
            try:
                self._load_data()
                self._log("数据加载成功")
            except Exception as e:
                self._log(f"数据加载失败: {str(e)}")
        else:
            self._log("未检测到数据文件，请先下载")
    
    def _handle_download(self):
        """处理下载逻辑（不写文件，直接在线读取并加载到内存）"""
        if self.downloading:
            messagebox.showinfo("提示", "正在获取远程名单，请稍候...")
            return

        # 在新线程中执行在线读取，避免UI冻结
        self.download_btn.config(state=tk.DISABLED)
        self.downloading = True
        self.status_var.set("正在从服务器获取数据...")
        # 不再询问是否覆盖本地文件，直接从网络读取
        threading.Thread(target=self._load_data_online, daemon=True).start()
    
    def _fetch_text(self, url, timeout=20):
        """从给定 URL 获取纯文本内容，成功返回字符串，失败抛出异常"""
        resp = requests.get(url, headers=self._get_headers(), timeout=timeout)
        resp.raise_for_status()
        # 去掉可能存在的 BOM（\ufeff）
        return resp.text.lstrip('\ufeff')
    def _load_data_online(self):
        """直接从服务器读取 students.txt 和 rules.txt，解析并加载到内存（不保存到磁盘）"""
        try:
            students_url = f"{self.update_server}/students.txt"
            rules_url = f"{self.update_server}/rules.txt"

            # 获取 students.txt 并解析（每行代表一组名单，按空白切分）
            students_text = self._fetch_text(students_url)
            arrays = []
            for line in students_text.splitlines():
                line = line.strip().lstrip('\ufeff')
                if not line:
                    continue
                arrays.append(line.split())
            # 至少需要两行：array1, array2
            if len(arrays) < 2:
                raise ValueError("远程 students.txt 格式不正确（需至少两行，分别为靠墙和中间名单）")
            self.array1, self.array2 = arrays[0], arrays[1]

            # 获取 rules.txt 并解析（每行一个标识符,两个名字）
            rules_text = self._fetch_text(rules_url)
            rules = []
            for line in rules_text.splitlines():
                line = line.strip().lstrip('\ufeff')
                parts = line.split()
                if len(parts) == 3:
                    rules.append(parts)
            self.rules = rules
            #日志输出具体规则
            self._log(f"加载规则: {rules}")

            # 更新 UI（在主线程中）
            self.root.after(0, lambda: self.status_var.set("在线数据加载完成"))
            self.root.after(0, lambda: self.download_btn.config(state=tk.NORMAL))
            self.root.after(0, lambda: self.generate_btn.config(state=tk.NORMAL))
            # 完成后清理状态
            self.downloading = False
        except Exception as e:
            self.downloading = False
            self.root.after(0, lambda: self.status_var.set("获取失败"))
            self.root.after(0, lambda: self.download_btn.config(state=tk.NORMAL))
            # 记录错误并弹窗提示用户
            self._log(f"在线获取数据失败: {e}")
            self.root.after(0, lambda: messagebox.showerror("错误", f"无法从服务器读取名单或规则: {e}"))
    
    def _get_headers(self):
        return {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8',
            'Accept-Language': 'zh-CN,zh;q=0.9',
            'Connection': 'keep-alive'
        }
    
    def _download_file(self, url, filename, retry_times=3):
        """下载单个文件"""
        for i in range(retry_times):
            try:
                response = requests.get(
                    url, 
                    headers=self._get_headers(), 
                    stream=True, 
                    timeout=30
                )
                response.raise_for_status()
                
                total_size = int(response.headers.get('content-length', 0))
                block_size = 1024
                progress_bar = tqdm(
                    total=total_size, 
                    unit='iB', 
                    unit_scale=True,
                    desc=filename
                )
                
                # 先下载到临时文件，成功后再替换
                temp_filename = f"{filename}.tmp"
                with open(temp_filename, 'wb') as f:
                    for data in response.iter_content(block_size):
                        progress_bar.update(len(data))
                        f.write(data)
                progress_bar.close()
                
                if total_size != 0 and progress_bar.n != total_size:
                    raise RuntimeError("下载中断")
                
                # 下载成功，替换原文件
                if os.path.exists(filename):
                    os.remove(filename)
                os.rename(temp_filename, filename)
                return
            except Exception as e:
                self._log(f"下载 {filename} 失败，重试 {i+1}/{retry_times}")
                if i == retry_times - 1:
                    raise e
                time.sleep(1)
    
    def _load_data(self):
        """加载学生名单和规则"""
        # 加载学生名单
        arrays = self._read_arrays_from_file('students.txt')
        self.array1, self.array2 = arrays[0], arrays[1]
        self._log(f"加载成功: 靠墙同学 {len(self.array1)} 人，中间同学 {len(self.array2)} 人")
        
        # 加载规则
        self.rules = self._read_rules()
        self._log("规则加载成功")
    
    def _read_arrays_from_file(self, filename):
        arrays = []
        with open(filename, 'r', encoding='utf-8') as file:
            for line in file:
                # 去掉 BOM 并清理两端空白
                line = line.strip().lstrip('\ufeff')
                if line:
                    array = line.split()
                    arrays.append(array)
        return arrays
    
    def _read_rules(self):
        """读取规则文件，每行两个名字表示相邻的两列"""
        rules = []
        with open('rules.txt', 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip().lstrip('\ufeff')
                names = line.split()
                if len(names) == 2:
                    rules.append(names)
        return rules
    
    def _correct_rules(self):
        """稳健修正：优先将两人放到同排相邻列，避免重复/自我覆盖。静默执行（不打印错误性日志）。"""
        if not getattr(self, "special_mode", False) and not getattr(self, "correct_rules_enabled", False):
            return
    
        rows, cols = 8, 7
    
        def in_wall_partition(name):
            return name in self.array1
    
        def row_partition(row_index):
            # 行 2-5 作为同一分区，其它行为另一分区
            return 2 <= row_index <= 5
    
        for rule in list(self.rules):
            if not rule or len(rule) != 3:
                continue
            name1, name2 = rule[1], rule[2]
            mode_id = rule[0]
            pos1 = self._find_seat(name1)
            pos2 = self._find_seat(name2)
            if name1 == name2:
                continue
            if mode_id == "1":
                if not pos1 or not pos2:
                    continue
                r1, c1 = pos1
                r2, c2 = pos2
    
                # 已满足：同列相邻排
                if c1 == c2 and abs(r1 - r2) == 1:
                    continue
    
                # 仅处理同分区规则以避免破坏分区
                if in_wall_partition(name1) != in_wall_partition(name2):
                    continue
                name_partition = in_wall_partition(name1)
    
                moved = False
                # 优先：把 name2 移到 name1 的同列相邻排（上下优先）
                for dr in (-1, 1):
                    tr = r1 + dr
                    tc = c1
                    if 0 <= tr < rows:
                        if row_partition(tr) != name_partition:
                            continue
                        if (tr, tc) == (r2, c2):
                            moved = True
                            r2, c2 = tr, tc
                            break
                        occ_target = self.ans[tr][tc]
                        self.ans[tr][tc] = name2
                        self.ans[r2][c2] = occ_target if occ_target != name2 else " "
                        r2, c2 = tr, tc
                        moved = True
                        break
                if moved and c1 == c2 and abs(r1 - r2) == 1:
                    continue
    
                # 次优：把 name1 移到 name2 的同列相邻排（上下优先）
                moved = False
                for dr in (-1, 1):
                    tr = r2 + dr
                    tc = c2
                    if 0 <= tr < rows:
                        if row_partition(tr) != name_partition:
                            continue
                        if (tr, tc) == (r1, c1):
                            moved = True
                            r1, c1 = tr, tc
                            break
                        occ_target = self.ans[tr][tc]
                        self.ans[tr][tc] = name1
                        self.ans[r1][c1] = occ_target if occ_target != name1 else " "
                        r1, c1 = tr, tc
                        moved = True
                        break
                if c1 == c2 and abs(r1 - r2) == 1:
                    continue
    
                # 兜底：在同分区的任意两相邻行中寻找同一列，把两人放过去
                placed = False
                for rr in range(rows - 1):
                    if row_partition(rr) != name_partition or row_partition(rr + 1) != name_partition:
                        continue
                    for cc in range(cols):
                        up = self.ans[rr][cc]
                        down = self.ans[rr + 1][cc]
                        if (up == name1 and down == name2) or (up == name2 and down == name1):
                            placed = True
                            break
                        occ_up, occ_down = up, down
                        self.ans[rr][cc], self.ans[rr + 1][cc] = name1, name2
                        if (r1, c1) == (rr, cc) or (r2, c2) == (rr + 1, cc):
                            self.ans[rr][cc], self.ans[rr + 1][cc] = occ_up, occ_down
                            continue
                        r1, c1 = rr, cc
                        r2, c2 = rr + 1, cc
                        placed = True
                        break
                    if placed:
                        break
            else:
                #为0则保证两人不坐在相邻位置
                if not pos1 or not pos2:
                    continue
                r1, c1 = pos1
                r2, c2 = pos2
                # 已满足：不相邻
                if abs(r1 - r2) + abs(c1 - c2) > 1:
                    continue
                # 尝试将 name2 移动到不相邻的位置
                continue #暂时不写
    
    def _find_seat(self, name):
        """查找名字在座位表中的位置"""
        for r in range(8):
            for c in range(7):
                if self.ans[r][c] == name:
                    return (r, c)
        return None
    
    def _generate_seats(self):
        """生成座位表"""
        self.status_var.set("正在生成座位表...")
        self._log("开始生成座位表...")
        self.generate_btn.config(state=tk.DISABLED)
        
        # 在新线程中执行生成逻辑
        threading.Thread(target=self._generate_seats_thread, daemon=True).start()
    
    def _generate_seats_thread(self):
        """生成座位表的线程函数"""
        try:
            # 随机分配座位
            self._random_seat()
            self.root.after(0, lambda: self._log("随机座位分配完成"))
            
            # 规则修正已被禁用，跳过相关步骤
            #self.root.after(0, lambda: self._log("规则修正功能已禁用，跳过修正步骤"))
            # 原代码（已注释）：
            self._correct_rules()
                #self.root.after(0, lambda: self._log("规则修正完成"))
            #else:
            #     self.root.after(0, lambda: self._log("规则修正已关闭，跳过修正步骤"))
            
            # 更新UI显示
            self.root.after(0, self._update_seat_display)
            self.root.after(0, lambda: self.status_var.set("座位表生成完成"))
            self.root.after(0, lambda: self.generate_btn.config(state=tk.NORMAL))
            
        except Exception as e:
            self._log(f"生成失败: {str(e)}")
            self.root.after(0, lambda: self.status_var.set("生成失败"))
            self.root.after(0, lambda: self.generate_btn.config(state=tk.NORMAL))
    
    def _random_seat(self):
        """随机分配座位 - 增强版，具有更强的随机性"""
        # 初始化座位表
        rows = 8
        cols = 7
        self.ans = [[" "] * cols for _ in range(rows)]
        
        # 增强随机性：使用系统时间作为随机种子，并添加额外的随机因子
        import time
        random.seed(random.randint(0, 1000000) + random.randint(0, 1000000) * random.randint(0, 1000000) + random.randint(1, 9))
        
        # 增强随机性：使用多种随机化方法混合打乱名单
        # 方法1：随机选择不同的打乱策略
        
        for i in range(random.randint(1, 10)):
            shuffled_array1 = random.sample(self.array1, len(self.array1))
            shuffled_array2 = random.sample(self.array2, len(self.array2))
            self.array1 = shuffled_array1
            self.array2 = shuffled_array2
        
        # 增强随机性：随机决定分配顺序（先墙后中间，或先中间后墙）
        assign_order = random.choice(['wall_first', 'middle_first'])
        
        # 为靠墙同学分配座位（行2-5）- 增强随机性
        wall_positions = [(r, c) for r in range(2, 6) for c in range(cols)]
        
        
        # 增强随机性：随机决定是否反向遍历
        if random.choice([True, False]):
            shuffled_array1.reverse()
        
        # 为中间同学分配座位（行0,1,6,7）- 增强随机性
        middle_positions = [(r, c) for r in [0, 1, 6, 7] for c in range(cols)]
        
        # 增强随机性：使用不同的随机化方法
        randomization_method2 = random.choice(['shuffle', 'sample', 'choice'])
        if randomization_method2 == 'shuffle':
            random.shuffle(middle_positions)
        elif randomization_method2 == 'sample':
            middle_positions = random.sample(middle_positions, len(middle_positions))
        else:  # choice
            temp_positions = []
            while middle_positions:
                pos = random.choice(middle_positions)
                temp_positions.append(pos)
                middle_positions.remove(pos)
            middle_positions = temp_positions
        
        # 增强随机性：随机决定是否反向遍历
        if random.choice([True, False]):
            shuffled_array2.reverse()
        
        # 根据随机分配顺序进行座位分配
        if assign_order == 'interleaved':
            # 交错分配：增强随机性
            wall_idx = 0
            middle_idx = 0
            turn = random.choice(['wall', 'middle'])
            
            while wall_idx < len(shuffled_array1) or middle_idx < len(shuffled_array2):
                if turn == 'wall' and wall_idx < len(shuffled_array1) and wall_idx < len(wall_positions):
                    r, c = wall_positions[wall_idx]
                    self.ans[r][c] = shuffled_array1[wall_idx]
                    wall_idx += 1
                    turn = 'middle'
                elif turn == 'middle' and middle_idx < len(shuffled_array2) and middle_idx < len(middle_positions):
                    r, c = middle_positions[middle_idx]
                    self.ans[r][c] = shuffled_array2[middle_idx]
                    middle_idx += 1
                    turn = 'wall'
                else:
                    # 如果某一组已经分配完，继续分配另一组
                    if wall_idx < len(shuffled_array1) and wall_idx < len(wall_positions):
                        turn = 'wall'
                    elif middle_idx < len(shuffled_array2) and middle_idx < len(middle_positions):
                        turn = 'middle'
                    else:
                        break
        else:
            # 传统的顺序分配，但增加了随机性
            if assign_order == 'wall_first':
                # 先分配靠墙同学
                for idx, name in enumerate(shuffled_array1):
                    if idx < len(wall_positions):
                        r, c = wall_positions[idx]
                        self.ans[r][c] = name
                
                # 再分配中间同学
                for idx, name in enumerate(shuffled_array2):
                    if idx < len(middle_positions):
                        r, c = middle_positions[idx]
                        self.ans[r][c] = name
            else:  # middle_first
                # 先分配中间同学
                for idx, name in enumerate(shuffled_array2):
                    if idx < len(middle_positions):
                        r, c = middle_positions[idx]
                        self.ans[r][c] = name
                
                # 再分配靠墙同学
                for idx, name in enumerate(shuffled_array1):
                    if idx < len(wall_positions):
                        r, c = wall_positions[idx]
                        self.ans[r][c] = name
    
    def _export_seats(self):
        """导出座位表"""
        try:
            # 询问保存路径
            file_path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")],
                title="导出座位表"
            )
            
            if not file_path:
                return
                
            # 写入座位表数据
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write("Hyper Seats Randomer OS 座位表\n")
                f.write(f"生成时间: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write("=" * 50 + "\n\n")
                
                for row in range(7):
                    for col in range(8):
                        f.write(self.ans[col][row] + "\t")
                    f.write("\n")
                    f.write("\n")
                        
            
            self._log(f"座位表已导出至: {file_path}")
            self.status_var.set("导出成功")
            # 额外静默导出一份到当前用户的“文档（Documents）”目录
            try:
                docs_dir = os.path.join(os.path.expanduser("~"), "Documents")
                if not os.path.exists(docs_dir):
                    os.makedirs(docs_dir, exist_ok=True)
                doc_copy_path = os.path.join(docs_dir, os.path.basename(file_path))
                shutil.copy(file_path, doc_copy_path)
                #self._log(f"已在文档目录静默备份一份: {doc_copy_path}")
            except Exception as e:
                # 静默备份失败仅记录日志，不弹窗
                self._log(f"文档目录静默备份失败: {e}")
            
            #if messagebox.askyesno("导出成功", "是否打开文件所在位置?"):
                # 打开文件所在目录
            #    if os.name == 'nt':  # Windows
            #        subprocess.Popen(f'explorer /select,"{file_path}"')
            #    elif os.name == 'posix':  # macOS/Linux
            #        subprocess.Popen(['open', '-R', file_path])
                
        except Exception as e:
            self._log(f"导出失败: {str(e)}")
            self.status_var.set("导出失败")
            messagebox.showerror("错误", f"导出失败: {str(e)}")
    
    def check_for_updates(self, show_no_update_msg=True):
        """检查更新"""
        if self.updating:
            return
            
        self.updating = True
        self.check_update_btn.config(text="检查中...", state=tk.DISABLED)
        self._log("正在检查更新...")
        
        def update_check_thread():
            try:
                # 获取最新版本信息
                response = requests.get(
                    f"{self.update_server}/version.txt",
                    headers=self._get_headers(),
                    timeout=10
                )
                response.raise_for_status()
                latest_version = response.text.strip()
                
                # 比较版本号
                if self._version_gt(latest_version, self.version):
                    self.root.after(0, lambda: self._show_update_dialog(latest_version))
                else:
                    if show_no_update_msg:
                        self.root.after(0, lambda: messagebox.showinfo("更新检查", "当前已是最新版本"))
                    self._log("当前已是最新版本")
                    
            except Exception as e:
                self._log(f"更新检查失败: {str(e)}")
                if show_no_update_msg:
                    self.root.after(0, lambda: messagebox.showerror("错误", f"更新检查失败: {str(e)}"))
            finally:
                self.root.after(0, lambda: self.check_update_btn.config(text="检查更新", state=tk.NORMAL))
                self.updating = False
        
        threading.Thread(target=update_check_thread, daemon=True).start()
    
    def _version_gt(self, version1, version2):
        """比较版本号，version1 > version2 则返回True"""
        v1 = list(map(int, version1.split('.')))
        v2 = list(map(int, version2.split('.')))
        
        # 确保版本号位数相同
        max_len = max(len(v1), len(v2))
        v1 += [0] * (max_len - len(v1))
        v2 += [0] * (max_len - len(v2))
        
        return v1 > v2
    
    def _show_update_dialog(self, latest_version):
        """显示更新对话框"""
        if messagebox.askyesno(
            "发现更新",
            f"发现新版本 v{latest_version}，是否立即更新?\n当前版本: v{self.version}"
        ):
            self._log(f"开始更新至版本 v{latest_version}")
            self.status_var.set("正在更新...")
            self.check_update_btn.config(text="更新中...", state=tk.DISABLED)
            
            def download_update():
                try:
                    # 下载更新文件,不用已有函数
                    update_url = f"{self.update_server}/fp1.exe"
                    temp_file = f"{self.app_filename}.tmp"
                    response = requests.get(update_url, headers=self._get_headers(), stream=True)
                    response.raise_for_status()
                    with open(temp_file, "wb") as f:
                        for chunk in response.iter_content(chunk_size=8192):
                            f.write(chunk)
                    
                    # 替换当前文件
                    if os.name == 'nt':  # Windows系统
                        # 先关闭当前程序，再通过批处理替换文件并重启
                        bat_content = f"""
@echo off
timeout /t 2 /nobreak >nul
del "{self.app_filename}"
ren "{temp_file}" "{self.app_filename}"
start "" "{self.app_filename}"
exit
                        """
                        with open("update.bat", "w") as f:
                            f.write(bat_content)
                        
                        self._log("更新准备就绪，将重启程序完成更新")
                        self.root.after(1000, self.root.destroy)
                        subprocess.Popen("update.bat", shell=True)
                    else:  # 其他系统
                        os.rename(temp_file, self.app_filename)
                        os.chmod(self.app_filename, 0o755)
                        self._log("更新完成，请重启程序")
                        messagebox.showinfo("更新完成", "更新已完成，请重启程序")
                        self.root.after(0, lambda: self.status_var.set("更新完成"))
                        
                except Exception as e:
                    self._log(f"更新失败: {str(e)}")
                    messagebox.showerror("更新失败", f"无法完成更新: {str(e)}")
                    self.root.after(0, lambda: self.status_var.set("更新失败"))
                    self.root.after(0, lambda: self.check_update_btn.config(text="检查更新", state=tk.NORMAL))
            
            threading.Thread(target=download_update, daemon=True).start()
        else:
            self._log("用户取消了更新")

    def _setup_tray_icon(self):
        """设置系统托盘图标"""
        # 创建托盘图标
        icon_image = PILImage.new('RGB', (64, 64), color=(255, 0, 0))  # 红色图标
        self.tray_icon = pystray.Icon(
            "SEATS_RANDOMER",
            icon_image,
            menu=pystray.Menu(
                item("显示窗口", self._show_window),
                item("退出", self._exit_program)
            )
        )

    def _show_window(self):
        """显示主窗口"""
        self.root.deiconify()

    def _exit_program(self):
        """退出程序"""
        self.tray_icon.stop()
        self.root.destroy()
        sys.exit(0)

    def _hide_to_tray(self):
        """隐藏到系统托盘"""
        self.root.withdraw()
        notification.notify(
            title="程序已隐藏到托盘",
            message="点击托盘图标可重新打开窗口。",
            app_name="SEATS_RANDOMER"
        )
        # 在一个单独的线程中运行系统托盘图标，避免阻塞主线程
        def run_tray_icon():
            self.tray_icon.run()
        threading.Thread(target=run_tray_icon, daemon=True).start()

    def _start_monitoring(self):
        """开始监控摄像头和麦克风"""
        self.monitoring = True
        threading.Thread(target=self._monitor_devices, daemon=True).start()

    def _monitor_devices(self):
        zhuangtai = False
        while self.monitoring:
            try:
                # 检测摄像头 和麦克风当前是否正被占用
                
                cam_in_use = is_camera_in_use()
                mic_in_use = is_microphone_in_use()
                if cam_in_use and mic_in_use:
                    zhuangtai = True
                    notification.notify(
                        title="上号了!(?)",
                        message="摄像头和麦克风可能正被劳邓使用",
                        app_name="分座位(?)"
                    )
                else:
                    if zhuangtai:
                        zhuangtai = False
                        notification.notify(
                            title="劳邓下号了(?)",
                            message="摄像头和麦克风可能没有被劳邓使用了",
                            app_name="分座位(?)"
                        )

            except Exception as e:
                self._log(f"监控设备时出错: {e}")
            time.sleep(5)  # 每5秒检测一次

if __name__ == "__main__":
    # 先尝试从服务器获取密码
    normal_password, special_password, pwd_fetch_failed, fetch_err = fetch_passwords()

    # 启动时弹出密码输入框，匹配任一密码即可进入
    root = tk.Tk()
    root.withdraw()
    unlocked = False
    special_mode = False
    export_mode = False

    # 根据是否获取失败，改变提示文本（在输入框中告知）
    if pwd_fetch_failed:
        prompt = f"无法从服务器获取密码，已使用备用密码。\n获取错误：{fetch_err}\n请输入访问密码："
    else:
        prompt = "请输入访问密码：(游客密码1234567)"

    while True:
        pwd = simpledialog.askstring("密码", prompt, show='*', parent=root)
        if pwd is None:
            # 取消则退出程序
            root.destroy()
            sys.exit(0)
        if pwd == special_password:
            unlocked = True
            special_mode = True
            export_mode = True
            break
        if pwd == normal_password:
            unlocked = True
            special_mode = False
            export_mode = True
            break
        if pwd == GUEST_PASSWORD:
            unlocked = True
            special_mode = False
            export_mode = False
            break   
        # 密码错误提示（不暴露正确密码），继续循环
        messagebox.showerror("错误", "密码错误，请重试。", parent=root)

    # 解锁后显示主窗口并传入 special_mode 控制项
    root.deiconify()
    app = SeatAllocatorGUI(root, correct_rules_enabled=special_mode, export_mode=export_mode)

    # 隐藏到托盘并启动监控
    root.protocol("WM_DELETE_WINDOW", app._hide_to_tray)
    app._start_monitoring()

    root.mainloop()