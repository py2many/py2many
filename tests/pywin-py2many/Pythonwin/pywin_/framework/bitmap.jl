using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import glob

import win32con

import string

include("app.jl")

using win32com_.gen_py.mfc: docview, window
abstract type AbstractBitmapDocument <: Abstractdocview.Document end
abstract type AbstractBitmapView <: Abstractdocview.ScrollView end
abstract type AbstractBitmapFrame <: Abstractwindow.MDIChildWnd end
abstract type AbstractBitmapTemplate <: Abstractdocview.DocTemplate end
bStretch = 1
mutable struct BitmapDocument <: AbstractBitmapDocument
    #= A bitmap document.  Holds the bitmap data itself. =#
    bitmap
    size

    BitmapDocument(template) = begin
        docview.Document.__init__(self, template)
        new(template)
    end
end
function OnNewDocument(self::BitmapDocument)
    MessageBox(win32ui, "Bitmaps can not be created.")
end

function OnOpenDocument(self::BitmapDocument, filename)::Int64
    self.bitmap = CreateBitmap(win32ui)
    f = readline(filename)
    try
        try
            LoadBitmapFile(self.bitmap, f)
        catch exn
            if exn isa IOError
                MessageBox(win32ui, "Could not load the bitmap from %s" % filename)
                return 0
            end
        end
    finally
        close(f)
    end
    self.size = GetSize(self.bitmap)
    return 1
end

function DeleteContents(self::BitmapDocument)
    self.bitmap = nothing
end

mutable struct BitmapView <: AbstractBitmapView
    #= A view of a bitmap.  Obtains data from document. =#
    width::Int64
    height::Int64

    BitmapView(doc) = begin
        docview.ScrollView.__init__(self, doc)
        HookMessage(OnSize, win32con.WM_SIZE)
        new(doc)
    end
end
function OnInitialUpdate(self::BitmapView)
    doc = GetDocument(self)
    if doc.bitmap
        bitmapSize = GetSize(doc.bitmap)
        SetScrollSizes(self, win32con.MM_TEXT, bitmapSize)
    end
end

function OnSize(self::BitmapView, params)
    lParam = params[4]
    self.width = LOWORD(win32api, lParam)
    self.height = HIWORD(win32api, lParam)
end

function OnDraw(self::BitmapView, dc)
    doc = GetDocument(self)
    if doc.bitmap === nothing
        return
    end
    bitmapSize = GetSize(doc.bitmap)
    if bStretch != 0
        viewRect = (0, 0, self.width, self.height)
        bitmapRect = (0, 0, bitmapSize[1], bitmapSize[2])
        Paint(doc.bitmap, dc, viewRect, bitmapRect)
    else
        Paint(doc.bitmap, dc)
    end
end

mutable struct BitmapFrame <: AbstractBitmapFrame
end
function OnCreateClient(self::BitmapFrame, createparams, context)::Int64
    borderX = GetSystemMetrics(win32api, win32con.SM_CXFRAME)
    borderY = GetSystemMetrics(win32api, win32con.SM_CYFRAME)
    titleY = GetSystemMetrics(win32api, win32con.SM_CYCAPTION)
    mdiClient = GetWindow(GetMainFrame(win32ui), win32con.GW_CHILD)
    clientWindowRect = ScreenToClient(mdiClient, GetWindowRect(mdiClient))
    clientWindowSize = (
        clientWindowRect[3] - clientWindowRect[1],
        clientWindowRect[4] - clientWindowRect[2],
    )
    left, top, right, bottom = ScreenToClient(mdiClient, GetWindowRect(self))
    OnCreateClient(window.MDIChildWnd, self, createparams)
    return 1
end

mutable struct BitmapTemplate <: AbstractBitmapTemplate
    BitmapTemplate() = begin
        docview.DocTemplate.__init__(
            self,
            win32ui.IDR_PYTHONTYPE,
            BitmapDocument,
            BitmapFrame,
            BitmapView,
        )
        new()
    end
end
function MatchDocType(self::BitmapTemplate, fileName, fileType)
    doc = FindOpenDocument(self, fileName)
    if doc
        return doc
    end
    ext = lower(splitext(os.path, fileName)[2])
    if ext == ".bmp"
        return win32ui.CDocTemplate_Confidence_yesAttemptNative
    end
    return win32ui.CDocTemplate_Confidence_maybeAttemptForeign
end

try
    RemoveDocTemplate(GetApp(win32ui), bitmapTemplate)
catch exn
    if exn isa NameError
        #= pass =#
    end
end
bitmapTemplate = BitmapTemplate()
SetDocStrings(
    bitmapTemplate,
    "\nBitmap\nBitmap\nBitmap (*.bmp)\n.bmp\nPythonBitmapFileType\nPython Bitmap File",
)
AddDocTemplate(GetApp(win32ui), bitmapTemplate)
function t()
    OpenDocumentFile(bitmapTemplate, "d:\\winnt\\arcade.bmp")
end

function demo()
    winDir = GetWindowsDirectory(win32api)
    for fileName in glob1(glob, winDir, "*.bmp")[begin:2]
        OpenDocumentFile(bitmapTemplate, join)
    end
end
