using Printf
using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")
include("daodump.jl")
import CheckClean

using win32com_.client: gencache, constants, Dispatch

function CreateTestAccessDatabase(dbname = nothing)
    if dbname === nothing
        dbname = join
    end
    access = Dispatch("Access.Application")
    dbEngine = access.DBEngine
    workspace = Workspaces(dbEngine, 0)
    try
        std::fs::remove_file(dbname)
    catch exn
        if exn isa os.error
            println(
                "WARNING - Unable to delete old test database - expect a COM exception RSN!",
            )
        end
    end
    newdb = CreateDatabase(workspace, dbname, constants.dbLangGeneral, constants.dbEncrypt)
    table = CreateTableDef(newdb, "Test Table 1")
    Append(table.Fields, CreateField(table, "First Name", constants.dbText))
    Append(table.Fields, CreateField(table, "Last Name", constants.dbText))
    index = CreateIndex(table, "UniqueIndex")
    Append(index.Fields, CreateField(index, "First Name"))
    Append(index.Fields, CreateField(index, "Last Name"))
    index.Unique = -1
    Append(table.Indexes, index)
    Append(newdb.TableDefs, table)
    table = CreateTableDef(newdb, "Test Table 2")
    Append(table.Fields, CreateField(table, "First Name", constants.dbText))
    Append(table.Fields, CreateField(table, "Last Name", constants.dbText))
    Append(newdb.TableDefs, table)
    relation = CreateRelation(newdb, "TestRelationship")
    relation.Table = "Test Table 1"
    relation.ForeignTable = "Test Table 2"
    field = CreateField(relation, "First Name")
    field.ForeignName = "First Name"
    Append(relation.Fields, field)
    field = CreateField(relation, "Last Name")
    field.ForeignName = "Last Name"
    Append(relation.Fields, field)
    relation.Attributes =
        constants.dbRelationDeleteCascade + constants.dbRelationUpdateCascade
    Append(newdb.Relations, relation)
    tab1 = OpenRecordset(newdb, "Test Table 1")
    AddNew(tab1)
    Fields(tab1, "First Name").Value = "Mark"
    Fields(tab1, "Last Name").Value = "Hammond"
    Update(tab1)
    MoveFirst(tab1)
    bk = tab1.Bookmark
    AddNew(tab1)
    Fields(tab1, "First Name").Value = "Second"
    Fields(tab1, "Last Name").Value = "Person"
    Update(tab1)
    MoveLast(tab1)
    if Fields(tab1, "First Name").Value != "Second"
        throw(RuntimeError("Unexpected record is last - makes bookmark test pointless!"))
    end
    tab1.Bookmark = bk
    if tab1.Bookmark != bk
        throw(RuntimeError("The bookmark data is not the same"))
    end
    if Fields(tab1, "First Name").Value != "Mark"
        throw(RuntimeError("The bookmark did not reset the record pointer correctly"))
    end
    return dbname
end

function DoDumpAccessInfo(dbname)
    a = nothing
    forms = nothing
    try
        write(sys.stderr, "Creating Access Application...\n")
        a = Dispatch("Access.Application")
        @printf("Opening database %s\n", dbname)
        OpenCurrentDatabase(a, dbname)
        db = CurrentDb(a)
        DumpDB(daodump, db, 1)
        forms = a.Forms
        @printf("There are %d forms open.\n", length(forms))
        reports = a.Reports
        @printf("There are %d reports open\n", length(reports))
    finally
        if !(a === nothing)
            write(sys.stderr, "Closing database\n")
            try
                CloseCurrentDatabase(a)
            catch exn
                if exn isa pythoncom.com_error
                    #= pass =#
                end
            end
        end
    end
end

function GenerateSupport()
    EnsureModule(gencache, "{00025E01-0000-0000-C000-000000000046}", 0, 4, 0)
    EnsureDispatch(gencache, "Access.Application")
end

function DumpAccessInfo(dbname)
    amod = GetModuleForProgID(gencache, "Access.Application")
    dmod = GetModuleForProgID(gencache, "DAO.DBEngine.35")
    if amod === nothing && dmod === nothing
        DoDumpAccessInfo(dbname)
        GenerateSupport()
    else
        write(
            sys.stderr,
            "testAccess not doing dynamic test, as generated code already exists\n",
        )
    end
    DoDumpAccessInfo(dbname)
end

function test(dbname = nothing)
    if dbname === nothing
        try
            GenerateSupport()
        catch exn
            if exn isa pythoncom.com_error
                println("*** Can not import the MSAccess type libraries - tests skipped")
                return
            end
        end
        dbname = CreateTestAccessDatabase()
        @printf("A test database at \'%s\' was created\n", dbname)
    end
    DumpAccessInfo(dbname)
end

if abspath(PROGRAM_FILE) == @__FILE__
    dbname = nothing
    if length(append!([PROGRAM_FILE], ARGS)) > 1
        dbname = append!([PROGRAM_FILE], ARGS)[2]
    end
    test(dbname)
    CheckClean()
end
