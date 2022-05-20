using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.mfc.dialog
import win32con
using win32com_.gen_py.mfc: afxres, window

abstract type AbstractDockingBar <: Abstractwindow.Wnd end
clrBtnHilight = GetSysColor(win32api, win32con.COLOR_BTNHILIGHT)
clrBtnShadow = GetSysColor(win32api, win32con.COLOR_BTNSHADOW)
function CenterPoint(rect)
    width = rect[3] - rect[1]
    height = rect[4] - rect[2]
    return (rect[1] + (width ÷ 2), rect[2] + (height ÷ 2))
end

function OffsetRect(rect, point)::Tuple
    x, y = point
    return (rect[1] + x, rect[2] + y, rect[3] + x, rect[4] + y)
end

function DeflateRect(rect, point)::Tuple
    x, y = point
    return (rect[1] + x, rect[2] + y, rect[3] - x, rect[4] - y)
end

function PtInRect(rect, pt)
    return rect[1] <= pt[1] < rect[3] && rect[2] <= pt[2] < rect[4]
end

mutable struct DockingBar <: AbstractDockingBar
    OnCaptureChanged
    OnLButtonDblClk
    OnLButtonDown
    OnLButtonUp
    OnMouseMove
    OnNcLButtonDblClk
    OnNcLButtonDown
    OnNcPaint
    OnWindowPosChanged
    _obj_
    bInRecalcNC::Int64
    bTracking::Int64
    brushBkgd
    cCaptionSize
    cMinHeight
    cMinWidth
    cxBorder::Int64
    cxEdge::Int64
    cxGripper::Int64
    cyBorder::Int64
    dialog
    dockBar
    nDockBarID::Int64
    ptOld
    rectBorder::Tuple{Int64}
    rectClose::Tuple{Int64}
    rectGripper::Tuple{Int64}
    rectTracker::Tuple{Int64}
    rectUndock::Tuple{Int64}
    sizeFloat::Tuple{Int64}
    sizeHorz::Tuple{Int64}
    sizeMin::Tuple{Int64}
    sizeVert::Tuple{Int64}
    obj

    DockingBar(obj = nothing) = begin
        if obj === nothing
            obj = win32ui.CreateControlBar()
        end
        window.Wnd.__init__(self, obj)
        brushBkgd.CreateSolidBrush(win32api.GetSysColor(win32con.COLOR_BTNFACE))
        new(obj)
    end
end
function OnUpdateCmdUI(self::DockingBar, target, bDisableIfNoHndler)
    return UpdateDialogControls(self, target, bDisableIfNoHndler)
end

function CreateWindow(
    self::DockingBar,
    parent,
    childCreator,
    title,
    id,
    style = (win32con.WS_CHILD | win32con.WS_VISIBLE) | afxres.CBRS_LEFT,
    childCreatorArgs = (),
)
    @assert(!(style & afxres.CBRS_SIZE_FIXED && style & afxres.CBRS_SIZE_DYNAMIC))
    self.rectClose = (0, 0, 0, 0)
    self.rectBorder = (0, 0, 0, 0)
    self.rectGripper = (0, 0, 0, 0)
    self.rectTracker = (0, 0, 0, 0)
    self._obj_.dwStyle = style & afxres.CBRS_ALL
    cursor = LoadCursor(win32api, 0, win32con.IDC_ARROW)
    wndClass = RegisterWndClass(
        win32ui,
        win32con.CS_DBLCLKS,
        cursor,
        GetSafeHandle(self.brushBkgd),
        0,
    )
    CreateWindow(self._obj_, wndClass, title, style, (0, 0, 0, 0), parent, id)
    self.dialog = childCreator((self,) + childCreatorArgs...)
    @assert(IsWindow(self.dialog))
    rect = GetWindowRect(self.dialog)
    self.sizeHorz = (rect[3] - rect[1], rect[4] - rect[2])
    self.sizeVert = (rect[3] - rect[1], rect[4] - rect[2])
    self.sizeFloat = (rect[3] - rect[1], rect[4] - rect[2])
    self.sizeHorz = (self.sizeHorz[1], (self.sizeHorz[2] + self.cxEdge) + self.cxBorder)
    self.sizeVert = ((self.sizeVert[1] + self.cxEdge) + self.cxBorder, self.sizeVert[2])
    HookMessages(self)
end

function CalcFixedLayout(self::DockingBar, bStretch, bHorz)::Tuple
    rectTop = GetWindowRect(GetControlBar(self.dockSite, afxres.AFX_IDW_DOCKBAR_TOP))
    rectLeft = GetWindowRect(GetControlBar(self.dockSite, afxres.AFX_IDW_DOCKBAR_LEFT))
    if bStretch
        nHorzDockBarWidth = 32767
        nVertDockBarHeight = 32767
    else
        nHorzDockBarWidth = (rectTop[3] - rectTop[1]) + 4
        nVertDockBarHeight = (rectLeft[4] - rectLeft[2]) + 4
    end
    if IsFloating(self)
        return self.sizeFloat
    end
    if bHorz
        return (nHorzDockBarWidth, self.sizeHorz[2])
    end
    return (self.sizeVert[1], nVertDockBarHeight)
end

function CalcDynamicLayout(self::DockingBar, length, mode)::Tuple
    if IsFloating(self)
        ModifyStyle(GetParent(GetParent(self)), win32ui.MFS_4THICKFRAME, 0)
    end
    if mode & (win32ui.LM_HORZDOCK | win32ui.LM_VERTDOCK)
        flags =
            (
                ((win32con.SWP_NOSIZE | win32con.SWP_NOMOVE) | win32con.SWP_NOZORDER) |
                win32con.SWP_NOACTIVATE
            ) | win32con.SWP_FRAMECHANGED
        SetWindowPos(self, 0, (0, 0, 0, 0), flags)
        RecalcLayout(self.dockSite)
        return CalcDynamicLayout(self._obj_, length, mode)
    end
    if mode & win32ui.LM_MRUWIDTH
        return self.sizeFloat
    end
    if mode & win32ui.LM_COMMIT
        self.sizeFloat = (length, self.sizeFloat[2])
        return self.sizeFloat
    end
    if IsFloating(self)
        dc = self.dockContext
        pt = GetCursorPos(win32api)
        windowRect = GetWindowRect(GetParent(GetParent(self)))
        hittest = dc.nHitTest
        if hittest == win32con.HTTOPLEFT
            cx = max(windowRect[3] - pt[1], self.cMinWidth) - self.cxBorder
            cy = max((windowRect[4] - self.cCaptionSize) - pt[2], self.cMinHeight) - 1
            self.sizeFloat = (cx, cy)
            top =
                min(pt[2], (windowRect[4] - self.cCaptionSize) - self.cMinHeight) -
                self.cyBorder
            left = min(pt[1], windowRect[3] - self.cMinWidth) - 1
            dc.rectFrameDragHorz =
                (left, top, dc.rectFrameDragHorz[3], dc.rectFrameDragHorz[4])
            return self.sizeFloat
        end
        if hittest == win32con.HTTOPRIGHT
            cx = max(pt[1] - windowRect[1], self.cMinWidth)
            cy = max((windowRect[4] - self.cCaptionSize) - pt[2], self.cMinHeight) - 1
            self.sizeFloat = (cx, cy)
            top =
                min(pt[2], (windowRect[4] - self.cCaptionSize) - self.cMinHeight) -
                self.cyBorder
            dc.rectFrameDragHorz = (
                dc.rectFrameDragHorz[1],
                top,
                dc.rectFrameDragHorz[3],
                dc.rectFrameDragHorz[4],
            )
            return self.sizeFloat
        end
        if hittest == win32con.HTBOTTOMLEFT
            cx = max(windowRect[3] - pt[1], self.cMinWidth) - self.cxBorder
            cy = max((pt[2] - windowRect[2]) - self.cCaptionSize, self.cMinHeight)
            self.sizeFloat = (cx, cy)
            left = min(pt[1], windowRect[3] - self.cMinWidth) - 1
            dc.rectFrameDragHorz = (
                left,
                dc.rectFrameDragHorz[2],
                dc.rectFrameDragHorz[3],
                dc.rectFrameDragHorz[4],
            )
            return self.sizeFloat
        end
        if hittest == win32con.HTBOTTOMRIGHT
            cx = max(pt[1] - windowRect[1], self.cMinWidth)
            cy = max((pt[2] - windowRect[2]) - self.cCaptionSize, self.cMinHeight)
            self.sizeFloat = (cx, cy)
            return self.sizeFloat
        end
    end
    if mode & win32ui.LM_LENGTHY
        self.sizeFloat = (self.sizeFloat[1], max(self.sizeMin[2], length))
        return self.sizeFloat
    else
        return (max(self.sizeMin[1], length), self.sizeFloat[2])
    end
end

function OnWindowPosChanged(self::DockingBar, msg)::Int64
    if GetSafeHwnd(self) == 0 || self.dialog === nothing
        return 0
    end
    lparam = msg[4]
    " LPARAM used with WM_WINDOWPOSCHANGED:\n\t\t\ttypedef struct {\n\t\t\t\tHWND hwnd;\n\t\t\t\tHWND hwndInsertAfter;\n\t\t\t\tint x;\n\t\t\t\tint y;\n\t\t\t\tint cx;\n\t\t\t\tint cy;\n\t\t\t\tUINT flags;} WINDOWPOS;\n\t\t"
    format = "PPiiiii"
    bytes = GetBytes(win32ui, lparam, calcsize(struct_, format))
    hwnd, hwndAfter, x, y, cx, cy, flags = unpack(struct_, format, bytes)
    if self.bInRecalcNC != 0
        rc = GetClientRect(self)
        MoveWindow(self.dialog, rc)
        return 0
    end
    nDockBarID = GetDlgCtrlID(GetParent(self))
    if nDockBarID == self.nDockBarID &&
       flags & win32con.SWP_NOSIZE &&
       (self._obj_.dwStyle & afxres.CBRS_BORDER_ANY) != afxres.CBRS_BORDER_ANY
        return
    end
    self.nDockBarID = nDockBarID
    self.bInRecalcNC = 1
    try
        swpflags =
            ((win32con.SWP_NOSIZE | win32con.SWP_NOMOVE) | win32con.SWP_NOZORDER) |
            win32con.SWP_FRAMECHANGED
        SetWindowPos(self, 0, (0, 0, 0, 0), swpflags)
    finally
        self.bInRecalcNC = 0
    end
    return 0
end

function OnSetCursor(self::DockingBar, window, nHitTest, wMouseMsg)::Int64
    if nHitTest != win32con.HTSIZE || self.bTracking
        return OnSetCursor(self._obj_, window, nHitTest, wMouseMsg)
    end
    if IsHorz(self)
        SetCursor(win32api, LoadCursor(win32api, 0, win32con.IDC_SIZENS))
    else
        SetCursor(win32api, LoadCursor(win32api, 0, win32con.IDC_SIZEWE))
    end
    return 1
end

function OnLButtonUp(self::DockingBar, msg)::Int64
    if !(self.bTracking) != 0
        return 1
    end
    StopTracking(self, 1)
    return 0
end

function OnLButtonDown(self::DockingBar, msg)::Int64
    if self.dockBar != nothing
        pt = msg[6]
        pt = ClientToScreen(self, pt)
        StartDrag(self.dockContext, pt)
        return 0
    end
    return 1
end

function OnNcLButtonDown(self::DockingBar, msg)::Int64
    if self.bTracking != 0
        return 0
    end
    nHitTest = msg[3]
    wparam = msg[3]
    pt = msg[6]
    if nHitTest == win32con.HTSYSMENU && !IsFloating(self)
        ShowControlBar(GetDockingFrame(self), self, 0, 0)
    elseif nHitTest == win32con.HTMINBUTTON && !IsFloating(self)
        ToggleDocking(self.dockContext)
    elseif nHitTest == win32con.HTCAPTION && !IsFloating(self) && self.dockBar != nothing
        StartDrag(self.dockContext, pt)
    elseif nHitTest == win32con.HTSIZE && !IsFloating(self)
        StartTracking(self)
    else
        return 1
    end
    return 0
end

function OnLButtonDblClk(self::DockingBar, msg)::Int64
    if self.dockBar != nothing
        ToggleDocking(self.dockContext)
        return 0
    end
    return 1
end

function OnNcLButtonDblClk(self::DockingBar, msg)::Int64
    nHitTest = msg[3]
    wparam = msg[3]
    if self.dockBar != nothing && nHitTest == win32con.HTCAPTION
        ToggleDocking(self.dockContext)
        return 0
    end
    return 1
end

function OnMouseMove(self::DockingBar, msg)::Int64
    flags = msg[3]
    wparam = msg[3]
    lparam = msg[4]
    if IsFloating(self) || !(self.bTracking)
        return 1
    end
    x = LOWORD(win32api, lparam)
    if (x & 32768) != 0
        x = x | -65536
    end
    y = HIWORD(win32api, lparam)
    if (y & 32768) != 0
        y = y | -65536
    end
    pt = (x, y)
    cpt = CenterPoint(self.rectTracker)
    pt = ClientToWnd(self, pt)
    if IsHorz(self)
        if cpt[2] != pt[2]
            OnInvertTracker(self, self.rectTracker)
            self.rectTracker = OffsetRect(self.rectTracker, (0, pt[2] - cpt[2]))
            OnInvertTracker(self, self.rectTracker)
        end
    elseif cpt[1] != pt[1]
        OnInvertTracker(self, self.rectTracker)
        self.rectTracker = OffsetRect(self.rectTracker, (pt[1] - cpt[1], 0))
        OnInvertTracker(self, self.rectTracker)
    end
    return 0
end

function OnNcCalcSize(self::DockingBar, bCalcValid, size_info)::Int64
    rc0, rc1, rc2, pos = size_info
    self.rectBorder = GetWindowRect(self)
    self.rectBorder =
        OffsetRect(self.rectBorder, (-(self.rectBorder[1]), -(self.rectBorder[2])))
    dwBorderStyle = self._obj_.dwStyle | afxres.CBRS_BORDER_ANY
    if self.nDockBarID == afxres.AFX_IDW_DOCKBAR_TOP
        dwBorderStyle = dwBorderStyle & ~(afxres.CBRS_BORDER_BOTTOM)
        rc0.left = rc0.left + self.cxGripper
        rc0.bottom = rc0.bottom - self.cxEdge
        rc0.top = rc0.top + self.cxBorder
        rc0.right = rc0.right - self.cxBorder
        self.rectBorder = (
            self.rectBorder[1],
            self.rectBorder[4] - self.cxEdge,
            self.rectBorder[3],
            self.rectBorder[4],
        )
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_BOTTOM
        dwBorderStyle = dwBorderStyle & ~(afxres.CBRS_BORDER_TOP)
        rc0.left = rc0.left + self.cxGripper
        rc0.top = rc0.top + self.cxEdge
        rc0.bottom = rc0.bottom - self.cxBorder
        rc0.right = rc0.right - self.cxBorder
        self.rectBorder = (
            self.rectBorder[1],
            self.rectBorder[2],
            self.rectBorder[3],
            self.rectBorder[2] + self.cxEdge,
        )
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_LEFT
        dwBorderStyle = dwBorderStyle & ~(afxres.CBRS_BORDER_RIGHT)
        rc0.right = rc0.right - self.cxEdge
        rc0.left = rc0.left + self.cxBorder
        rc0.bottom = rc0.bottom - self.cxBorder
        rc0.top = rc0.top + self.cxGripper
        self.rectBorder = (
            self.rectBorder[3] - self.cxEdge,
            self.rectBorder[2],
            self.rectBorder[3],
            self.rectBorder[4],
        )
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_RIGHT
        dwBorderStyle = dwBorderStyle & ~(afxres.CBRS_BORDER_LEFT)
        rc0.left = rc0.left + self.cxEdge
        rc0.right = rc0.right - self.cxBorder
        rc0.bottom = rc0.bottom - self.cxBorder
        rc0.top = rc0.top + self.cxGripper
        self.rectBorder = (
            self.rectBorder[1],
            self.rectBorder[2],
            self.rectBorder[1] + self.cxEdge,
            self.rectBorder[4],
        )
    else
        self.rectBorder = (0, 0, 0, 0)
    end
    SetBarStyle(self, dwBorderStyle)
    return 0
end

function OnNcPaint(self::DockingBar, msg)::Int64
    EraseNonClient(self)
    dc = GetWindowDC(self)
    ctl = GetSysColor(win32api, win32con.COLOR_BTNHIGHLIGHT)
    cbr = GetSysColor(win32api, win32con.COLOR_BTNSHADOW)
    Draw3dRect(dc, self.rectBorder, ctl, cbr)
    DrawGripper(self, dc)
    rect = GetClientRect(self)
    InvalidateRect(self, rect, 1)
    return 0
end

function OnNcHitTest(self::DockingBar, pt)::Int64
    if IsFloating(self)
        return 1
    end
    ptOrig = pt
    rect = GetWindowRect(self)
    pt = (pt[1] - rect[1], pt[2] - rect[2])
    if PtInRect(self.rectClose, pt)
        return win32con.HTSYSMENU
    elseif PtInRect(self.rectUndock, pt)
        return win32con.HTMINBUTTON
    elseif PtInRect(self.rectGripper, pt)
        return win32con.HTCAPTION
    elseif PtInRect(self.rectBorder, pt)
        return win32con.HTSIZE
    else
        return OnNcHitTest(self._obj_, ptOrig)
    end
end

function StartTracking(self::DockingBar)
    SetCapture(self)
    RedrawWindow(self, nothing, nothing, win32con.RDW_ALLCHILDREN | win32con.RDW_UPDATENOW)
    LockWindowUpdate(self.dockSite)
    self.ptOld = CenterPoint(self.rectBorder)
    self.bTracking = 1
    self.rectTracker = self.rectBorder
    if !IsHorz(self)
        l, t, r, b = self.rectTracker
        b = b - 4
        self.rectTracker = (l, t, r, b)
    end
    OnInvertTracker(self, self.rectTracker)
end

function OnCaptureChanged(self::DockingBar, msg)::Int64
    hwnd = msg[4]
    lparam = msg[4]
    if self.bTracking && hwnd != GetSafeHwnd(self)
        StopTracking(self, 0)
    end
    return 1
end

function StopTracking(self::DockingBar, bAccept)::Int64
    OnInvertTracker(self, self.rectTracker)
    UnlockWindowUpdate(self.dockSite)
    self.bTracking = 0
    ReleaseCapture(self)
    if !(bAccept)
        return
    end
    rcc = GetWindowRect(self.dockSite)
    if IsHorz(self)
        newsize = self.sizeHorz[2]
        maxsize = newsize + (rcc[4] - rcc[2])
        minsize = self.sizeMin[2]
    else
        newsize = self.sizeVert[1]
        maxsize = newsize + (rcc[3] - rcc[1])
        minsize = self.sizeMin[1]
    end
    pt = CenterPoint(self.rectTracker)
    if self.nDockBarID == afxres.AFX_IDW_DOCKBAR_TOP
        newsize = newsize + (pt[2] - self.ptOld[2])
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_BOTTOM
        newsize = newsize + (-(pt[2]) + self.ptOld[2])
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_LEFT
        newsize = newsize + (pt[1] - self.ptOld[1])
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_RIGHT
        newsize = newsize + (-(pt[1]) + self.ptOld[1])
    end
    newsize = max(minsize, min(maxsize, newsize))
    if IsHorz(self)
        self.sizeHorz = (self.sizeHorz[1], newsize)
    else
        self.sizeVert = (newsize, self.sizeVert[2])
    end
    RecalcLayout(self.dockSite)
    return 0
end

function OnInvertTracker(self::DockingBar, rect)
    @assert((rect[3] - rect[1]) > 0 && (rect[4] - rect[2]) > 0)
    @assert(self.bTracking)
    rcc = GetWindowRect(self)
    rcf = GetWindowRect(self.dockSite)
    rect = OffsetRect(rect, (rcc[1] - rcf[1], rcc[2] - rcf[2]))
    rect = DeflateRect(rect, (1, 1))
    flags = (win32con.DCX_WINDOW | win32con.DCX_CACHE) | win32con.DCX_LOCKWINDOWUPDATE
    dc = GetDCEx(self.dockSite, nothing, flags)
    try
        brush = GetHalftoneBrush(win32ui)
        oldBrush = SelectObject(dc, brush)
        PatBlt(
            dc,
            (rect[1], rect[2]),
            (rect[3] - rect[1], rect[4] - rect[2]),
            win32con.PATINVERT,
        )
        SelectObject(dc, oldBrush)
    finally
        ReleaseDC(self.dockSite, dc)
    end
end

function IsHorz(self::DockingBar)
    return self.nDockBarID == afxres.AFX_IDW_DOCKBAR_TOP ||
           self.nDockBarID == afxres.AFX_IDW_DOCKBAR_BOTTOM
end

function ClientToWnd(self::DockingBar, pt)::Tuple
    x, y = pt
    if self.nDockBarID == afxres.AFX_IDW_DOCKBAR_BOTTOM
        y = y + self.cxEdge
    elseif self.nDockBarID == afxres.AFX_IDW_DOCKBAR_RIGHT
        x = x + self.cxEdge
    end
    return (x, y)
end

function DrawGripper(self::DockingBar, dc)
    if self._obj_.dwStyle & afxres.CBRS_FLOATING
        return
    end
    RecalcLayout(self.dockSite)
    gripper = GetWindowRect(self)
    gripper = ScreenToClient(self, gripper)
    gripper = OffsetRect(gripper, (-(gripper[1]), -(gripper[2])))
    gl, gt, gr, gb = gripper
    if self._obj_.dwStyle & afxres.CBRS_ORIENT_HORZ
        self.rectGripper = (gl, gt + 40, gl + 20, gb)
        self.rectClose = (gl + 7, gt + 10, gl + 19, gt + 22)
        DrawFrameControl(
            dc,
            self.rectClose,
            win32con.DFC_CAPTION,
            win32con.DFCS_CAPTIONCLOSE,
        )
        self.rectUndock = OffsetRect(self.rectClose, (0, 13))
        DrawFrameControl(
            dc,
            self.rectUndock,
            win32con.DFC_CAPTION,
            win32con.DFCS_CAPTIONMAX,
        )
        gt = gt + 38
        gb = gb - 10
        gl = gl + 10
        gr = gl + 3
        gripper = (gl, gt, gr, gb)
        Draw3dRect(dc, gripper, clrBtnHilight, clrBtnShadow)
        Draw3dRect(dc, OffsetRect(gripper, (4, 0)), clrBtnHilight, clrBtnShadow)
    else
        self.rectGripper = (gl, gt, gr - 40, gt + 20)
        self.rectClose = (gr - 21, gt + 7, gr - 10, gt + 18)
        DrawFrameControl(
            dc,
            self.rectClose,
            win32con.DFC_CAPTION,
            win32con.DFCS_CAPTIONCLOSE,
        )
        self.rectUndock = OffsetRect(self.rectClose, (-13, 0))
        DrawFrameControl(
            dc,
            self.rectUndock,
            win32con.DFC_CAPTION,
            win32con.DFCS_CAPTIONMAX,
        )
        gr = gr - 38
        gl = gl + 10
        gt = gt + 10
        gb = gt + 3
        gripper = (gl, gt, gr, gb)
        Draw3dRect(dc, gripper, clrBtnHilight, clrBtnShadow)
        Draw3dRect(dc, OffsetRect(gripper, (0, 4)), clrBtnHilight, clrBtnShadow)
    end
end

function HookMessages(self::DockingBar)
    HookMessage(self, self.OnLButtonUp, win32con.WM_LBUTTONUP)
    HookMessage(self, self.OnLButtonDown, win32con.WM_LBUTTONDOWN)
    HookMessage(self, self.OnLButtonDblClk, win32con.WM_LBUTTONDBLCLK)
    HookMessage(self, self.OnNcLButtonDown, win32con.WM_NCLBUTTONDOWN)
    HookMessage(self, self.OnNcLButtonDblClk, win32con.WM_NCLBUTTONDBLCLK)
    HookMessage(self, self.OnMouseMove, win32con.WM_MOUSEMOVE)
    HookMessage(self, self.OnNcPaint, win32con.WM_NCPAINT)
    HookMessage(self, self.OnCaptureChanged, win32con.WM_CAPTURECHANGED)
    HookMessage(self, self.OnWindowPosChanged, win32con.WM_WINDOWPOSCHANGED)
end

function EditCreator(parent)
    d = CreateEdit(win32ui)
    es =
        (
            ((win32con.WS_CHILD | win32con.WS_VISIBLE) | win32con.WS_BORDER) |
            win32con.ES_MULTILINE
        ) | win32con.ES_WANTRETURN
    CreateWindow(d, es, (0, 0, 150, 150), parent, 1000)
    return d
end

function test()
    global bar
    bar = DockingBar()
    creator = EditCreator
    CreateWindow(bar, GetMainFrame(win32ui), creator, "Coolbar Demo", 1048575)
    SetBarStyle(
        bar,
        ((GetBarStyle(bar) | afxres.CBRS_TOOLTIPS) | afxres.CBRS_FLYBY) |
        afxres.CBRS_SIZE_DYNAMIC,
    )
    EnableDocking(bar, afxres.CBRS_ALIGN_ANY)
    DockControlBar(GetMainFrame(win32ui), bar, afxres.AFX_IDW_DOCKBAR_BOTTOM)
end

if abspath(PROGRAM_FILE) == @__FILE__
    test()
end
