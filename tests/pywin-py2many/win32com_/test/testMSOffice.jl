using PyCall
pythoncom = pyimport("pythoncom")
pywintypes = pyimport("pywintypes")
win32api = pyimport("win32api")
import win32com_.test.Generated4Test.msword8

import xl5en32
import win32com_
import string
import win32com_.client.dynamic
using win32com_.test.util: CheckClean

using win32com_.client: gencache

error = "MSOffice test error"
function TestWord()
    try
        println("Starting Word 8 for dynamic test")
        word = Dispatch(win32com_.client.dynamic, "Word.Application")
        TestWord8(word)
        word = nothing
        println("Starting Word 8 for non-lazy dynamic test")
        dispatch = _GetGoodDispatch(win32com_.client.dynamic, "Word.Application")
        typeinfo = GetTypeInfo(dispatch)
        attr = GetTypeAttr(typeinfo)
        olerepr = DispatchItem(win32com_.client.build, typeinfo, attr, nothing, 0)
        word = CDispatch(win32com_.client.dynamic, dispatch, olerepr)
        dispatch = nothing
        typeinfo = nothing
        attr = nothing
        olerepr = nothing
        TestWord8(word)
    catch exn
        if exn isa pythoncom.com_error
            println("Starting Word 7 for dynamic test")
            word = Dispatch(win32com_.client, "Word.Basic")
            TestWord7(word)
        end
        let e = exn
            if e isa Exception
                println("Word dynamic tests failed$(e)")
                current_exceptions() != [] ? current_exceptions()[end] : nothing
            end
        end
    end
    println("Starting MSWord for generated test")
    try
        word = EnsureDispatch(gencache, "Word.Application.8")
        TestWord8(word)
    catch exn
        let e = exn
            if e isa Exception
                println("Word generated tests failed$(e)")
                current_exceptions() != [] ? current_exceptions()[end] : nothing
            end
        end
    end
end

function TestWord7(word)
    FileNew(word)
    if !AppShow(word)
        _proc_(word, "AppShow")
    end
    for i = 0:11
        FormatFont(word, i + 1, i + 12)
        Insert(word, "Hello from Python %d\n" % i)
    end
    FileClose(word, 2)
end

function TestWord8(word)
    word.Visible = 1
    doc = Add(word.Documents)
    wrange = Range(doc)
    for i = 0:9
        InsertAfter(wrange, "Hello from Python %d\n" % i)
    end
    paras = doc.Paragraphs
    for i = 0:length(paras)-1
        p = paras(i + 1)
        p.Font.ColorIndex = i + 1
        p.Font.Size = 12 + 4 * i
    end
    Close(doc, 0)
    Quit(word)
    Sleep(win32api, 1000)
end

function TestWord8OldStyle()
    try
    catch exn
        if exn isa ImportError
            println("Can not do old style test")
        end
    end
end

function TextExcel(xl)
    xl.Visible = 0
    if xl.Visible
        throw(error("Visible property is true."))
    end
    xl.Visible = 1
    if !(xl.Visible)
        throw(error("Visible property not true."))
    end
    if parse(Int, xl.Version[1]) >= 8
        Add(xl.Workbooks)
    else
        Add(Workbooks(xl))
    end
    Range(xl, "A1:C1").Value = (1, 2, 3)
    Range(xl, "A2:C2").Value = ("x", "y", "z")
    Range(xl, "A3:C3").Value = ("3", "2", "1")
    for i = 0:19
        Cells(xl, i + 1, i + 1).Value = "Hi %d" % i
    end
    if Range(xl, "A1").Value != "Hi 0"
        throw(error("Single cell range failed"))
    end
    if Range(xl, "A1:B1").Value != ((Unicode("Hi 0"), 2),)
        throw(error("flat-horizontal cell range failed"))
    end
    if Range(xl, "A1:A2").Value != ((Unicode("Hi 0"),), (Unicode("x"),))
        throw(error("flat-vertical cell range failed"))
    end
    if Range(xl, "A1:C3").Value != (
        (Unicode("Hi 0"), 2, 3),
        (Unicode("x"), Unicode("Hi 1"), Unicode("z")),
        (3, 2, Unicode("Hi 2")),
    )
        throw(error("square cell range failed"))
    end
    Range(xl, "A1:C3").Value = ((3, 2, 1), ("x", "y", "z"), (1, 2, 3))
    if Range(xl, "A1:C3").Value !=
       ((3, 2, 1), (Unicode("x"), Unicode("y"), Unicode("z")), (1, 2, 3))
        throw(error("Range was not what I set it to!"))
    end
    Cells(xl, 5, 1).Value = "Excel time"
    Cells(xl, 5, 2).Formula = "=Now()"
    Cells(xl, 6, 1).Value = "Python time"
    Cells(xl, 6, 2).Value = MakeTime(pythoncom, pylib::time())
    Cells(xl, 6, 2).NumberFormat = "d/mm/yy h:mm"
    AutoFit(None.EntireColumn)
    Close(Workbooks(xl, 1), 0)
    Quit(xl)
end

function TestAll()
    TestWord()
    try
        println("Starting Excel for Dynamic test...")
        xl = Dispatch(win32com_.client.dynamic, "Excel.Application")
        TextExcel(xl)
    catch exn
        let e = exn
            if e isa Exception
                worked = false
                println("Excel tests failed$(e)")
                current_exceptions() != [] ? current_exceptions()[end] : nothing
            end
        end
    end
    try
        println("Starting Excel 8 for generated excel8.py test...")
        mod = EnsureModule(gencache, "{00020813-0000-0000-C000-000000000046}", 0, 1, 2, 1)
        xl = Dispatch(win32com_.client, "Excel.Application")
        TextExcel(xl)
    catch exn
        if exn isa ImportError
            println("Could not import the generated Excel 97 wrapper")
        end
        let e = exn
            if e isa Exception
                println("Generated Excel tests failed$(e)")
                current_exceptions() != [] ? current_exceptions()[end] : nothing
            end
        end
    end
    try
        mod = EnsureModule(gencache, "{00020813-0000-0000-C000-000000000046}", 9, 1, 0)
        xl = Dispatch(win32com_.client, "Excel.Application.5")
        println("Starting Excel 95 for makepy test...")
        TextExcel(xl)
    catch exn
        if exn isa ImportError
            println("Could not import the generated Excel 95 wrapper")
        end
        let e = exn
            if e isa Exception
                println("Excel 95 tests failed$(e)")
                current_exceptions() != [] ? current_exceptions()[end] : nothing
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    TestAll()
    CheckClean()
    CoUninitialize(pythoncom)
end
