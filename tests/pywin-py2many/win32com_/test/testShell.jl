using PyCall
datetime = pyimport("datetime")
pywintypes = pyimport("pywintypes")
pythoncom = pyimport("pythoncom")
import tempfile

import copy

import win32timezone
try
    sys_maxsize = sys.maxsize
catch exn
    if exn isa AttributeError
        sys_maxsize = sys.maxint
    end
end
import win32con

using win32com_.shell: shell
using win32com_.shell.shellcon: *
using win32com_.storagecon: *
import win32com_.test.util
abstract type AbstractShellTester <: Abstractwin32com_.test.util.TestCase end
abstract type AbstractPIDLTester <: Abstractwin32com_.test.util.TestCase end
abstract type AbstractFILEGROUPDESCRIPTORTester <: Abstractwin32com_.test.util.TestCase end
abstract type AbstractFileOperationTester <: Abstractwin32com_.test.util.TestCase end
using pywin32_testutil: str2bytes
mutable struct ShellTester <: AbstractShellTester
end
function testShellLink(self::ShellTester)
    desktop = string(SHGetSpecialFolderPath(shell, 0, CSIDL_DESKTOP))
    num = 0
    shellLink = CoCreateInstance(
        pythoncom,
        shell.CLSID_ShellLink,
        nothing,
        pythoncom.CLSCTX_INPROC_SERVER,
        shell.IID_IShellLink,
    )
    persistFile = QueryInterface(shellLink, pythoncom.IID_IPersistFile)
    names = [join for n in listdir(os, desktop)]
    programs = string(SHGetSpecialFolderPath(shell, 0, CSIDL_PROGRAMS))
    extend(names, [join for n in listdir(os, programs)])
    for name in names
        try
            Load(persistFile, name, STGM_READ)
        catch exn
            if exn isa pythoncom.com_error
                continue
            end
        end
        fname, findData = GetPath(shellLink, 0)
        unc = GetPath(shellLink, shell.SLGP_UNCPRIORITY)[1]
        num += 1
    end
    if num == 0
        println(
            "Could not find any links on your desktop or programs dir, which is unusual",
        )
    end
end

function testShellFolder(self::ShellTester)
    sf = SHGetDesktopFolder(shell)
    names_1 = []
    for i in sf
        name = GetDisplayNameOf(sf, i, SHGDN_NORMAL)
        push!(names_1, name)
    end
    enum =
        EnumObjects(sf, 0, (SHCONTF_FOLDERS | SHCONTF_NONFOLDERS) | SHCONTF_INCLUDEHIDDEN)
    names_2 = []
    for i in enum
        name = GetDisplayNameOf(sf, i, SHGDN_NORMAL)
        push!(names_2, name)
    end
    sort(names_1)
    sort(names_2)
    assertEqual(self, names_1, names_2)
end

mutable struct PIDLTester <: AbstractPIDLTester
end
function _rtPIDL(self::PIDLTester, pidl)
    pidl_str = PIDLAsString(shell, pidl)
    pidl_rt = StringAsPIDL(shell, pidl_str)
    assertEqual(self, pidl_rt, pidl)
    pidl_str_rt = PIDLAsString(shell, pidl_rt)
    assertEqual(self, pidl_str_rt, pidl_str)
end

function _rtCIDA(self::PIDLTester, parent, kids)
    cida = (parent, kids)
    cida_str = CIDAAsString(shell, cida)
    cida_rt = StringAsCIDA(shell, cida_str)
    assertEqual(self, cida, cida_rt)
    cida_str_rt = CIDAAsString(shell, cida_rt)
    assertEqual(self, cida_str_rt, cida_str)
end

function testPIDL(self::PIDLTester)
    expect = str2bytes("\000\000\000")
    assertEqual(self, PIDLAsString(shell, [str2bytes("")]), expect)
    _rtPIDL(self, [str2bytes("\000")])
    _rtPIDL(self, [str2bytes(""), str2bytes(""), str2bytes("")])
    _rtPIDL(self, repeat([str2bytes("\000") * 2048], 2048))
    assertRaises(self, TypeError, shell.PIDLAsString, "foo")
end

function testCIDA(self::PIDLTester)
    _rtCIDA(self, [str2bytes("\000")], [[str2bytes("\000")]])
    _rtCIDA(self, [str2bytes("")], [[str2bytes("")]])
    _rtCIDA(
        self,
        [str2bytes("\000")],
        [[str2bytes("\000")], [str2bytes("")], [str2bytes("")]],
    )
end

function testBadShortPIDL(self::PIDLTester)
    pidl = str2bytes("\000")
    assertRaises(self, ValueError, shell.StringAsPIDL, pidl)
end

mutable struct FILEGROUPDESCRIPTORTester <: AbstractFILEGROUPDESCRIPTORTester
end
function _getTestTimes(self::FILEGROUPDESCRIPTORTester)::Tuple
    if pywintypes.TimeType <: datetime.datetime
        ctime = now(win32timezone)
        ctime = replace(ctime, (ctime.microsecond ÷ 1000) * 1000)
        atime = ctime + timedelta(datetime, 1)
        wtime = atime + timedelta(datetime, 1)
    else
        ctime = Time(pywintypes, 11)
        atime = Time(pywintypes, 12)
        wtime = Time(pywintypes, 13)
    end
    return (ctime, atime, wtime)
end

function _testRT(self::FILEGROUPDESCRIPTORTester, fd)
    fgd_string = FILEGROUPDESCRIPTORAsString(shell, [fd])
    fd2 = StringAsFILEGROUPDESCRIPTOR(shell, fgd_string)[1]
    fd = copy(fd)
    fd2 = copy(fd2)
    if "dwFlags" ∉ fd
        #Delete Unsupported
        del(fd2)
    end
    if "cFileName" ∉ fd
        assertEqual(self, fd2["cFileName"], "")
        #Delete Unsupported
        del(fd2)
    end
    assertEqual(self, fd, fd2)
end

function _testSimple(self::FILEGROUPDESCRIPTORTester, make_unicode)
    fgd = FILEGROUPDESCRIPTORAsString(shell, [], make_unicode)
    header = pack(struct_, "i", 0)
    assertEqual(self, header, fgd[begin:length(header)])
    _testRT(self, dict())
    d = dict()
    fgd = FILEGROUPDESCRIPTORAsString(shell, [d], make_unicode)
    header = pack(struct_, "i", 1)
    assertEqual(self, header, fgd[begin:length(header)])
    _testRT(self, d)
end

function testSimpleBytes(self::FILEGROUPDESCRIPTORTester)
    _testSimple(self, false)
end

function testSimpleUnicode(self::FILEGROUPDESCRIPTORTester)
    _testSimple(self, true)
end

function testComplex(self::FILEGROUPDESCRIPTORTester)
    clsid = MakeIID(pythoncom, "{CD637886-DB8B-4b04-98B5-25731E1495BE}")
    ctime, atime, wtime = _getTestTimes(self)
    d = dict(
        "foo.txt",
        clsid,
        (1, 2),
        (3, 4),
        win32con.FILE_ATTRIBUTE_NORMAL,
        ctime,
        atime,
        wtime,
        sys_maxsize + 1,
    )
    _testRT(self, d)
end

function testUnicode(self::FILEGROUPDESCRIPTORTester)
    ctime, atime, wtime = _getTestTimes(self)
    d = [
        dict(
            "foo.txt",
            (1, 2),
            (3, 4),
            win32con.FILE_ATTRIBUTE_NORMAL,
            ctime,
            atime,
            wtime,
            sys_maxsize + 1,
        ),
        dict(
            "foo2.txt",
            (1, 2),
            (3, 4),
            win32con.FILE_ATTRIBUTE_NORMAL,
            ctime,
            atime,
            wtime,
            sys_maxsize + 1,
        ),
        dict(
            "foo©.txt",
            (1, 2),
            (3, 4),
            win32con.FILE_ATTRIBUTE_NORMAL,
            ctime,
            atime,
            wtime,
            sys_maxsize + 1,
        ),
    ]
    s = FILEGROUPDESCRIPTORAsString(shell, d, 1)
    d2 = StringAsFILEGROUPDESCRIPTOR(shell, s)
    for t in d2
        #Delete Unsupported
        del(t)
    end
    assertEqual(self, d, d2)
end

mutable struct FileOperationTester <: AbstractFileOperationTester
    src_name
    dest_name
    test_data
end
function setUp(self::FileOperationTester)
    self.src_name = join
    self.dest_name = join
    self.test_data = str2bytes("Hello from\000Python")
    f = readline(self.src_name)
    write(f, self.test_data)
    close(f)
    try
        std::fs::remove_file(self.dest_name)
    catch exn
        if exn isa os.error
            #= pass =#
        end
    end
end

function tearDown(self::FileOperationTester)
    for fname in (self.src_name, self.dest_name)
        if isfile(os.path, fname)
            std::fs::remove_file(fname)
        end
    end
end

function testCopy(self::FileOperationTester)
    s = (0, FO_COPY, self.src_name, self.dest_name)
    rc, aborted = SHFileOperation(shell, s)
    assertTrue(self, !(aborted))
    assertEqual(self, 0, rc)
    assertTrue(self, isfile(os.path, self.src_name))
    assertTrue(self, isfile(os.path, self.dest_name))
end

function testRename(self::FileOperationTester)
    s = (0, FO_RENAME, self.src_name, self.dest_name)
    rc, aborted = SHFileOperation(shell, s)
    assertTrue(self, !(aborted))
    assertEqual(self, 0, rc)
    assertTrue(self, isfile(os.path, self.dest_name))
    assertTrue(self, !isfile(os.path, self.src_name))
end

function testMove(self::FileOperationTester)
    s = (0, FO_MOVE, self.src_name, self.dest_name)
    rc, aborted = SHFileOperation(shell, s)
    assertTrue(self, !(aborted))
    assertEqual(self, 0, rc)
    assertTrue(self, isfile(os.path, self.dest_name))
    assertTrue(self, !isfile(os.path, self.src_name))
end

function testDelete(self::FileOperationTester)
    s = (0, FO_DELETE, self.src_name, nothing, FOF_NOCONFIRMATION)
    rc, aborted = SHFileOperation(shell, s)
    assertTrue(self, !(aborted))
    assertEqual(self, 0, rc)
    assertTrue(self, !isfile(os.path, self.src_name))
end

if abspath(PROGRAM_FILE) == @__FILE__
    testmain(win32com_.test.util)
end
