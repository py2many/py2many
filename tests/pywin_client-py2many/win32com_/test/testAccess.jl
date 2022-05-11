module testAccess
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
include("daodump.jl")
using util: CheckClean

using win32com.client: gencache, constants, Dispatch


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
println("WARNING - Unable to delete old test database - expect a COM exception RSN!")
end
end
newdb = CreateDatabase(workspace, dbname, constants.dbLangGeneral, constants.dbEncrypt)
table = CreateTableDef(newdb, "Test Table 1")
Append(table.Fields, CreateField(table, "First Name", constants.dbText))
Append(table.Fields, CreateField(table, "Last Name", constants.dbText))
index = CreateIndex(table, "UniqueIndex")
Append(index.Fields, CreateField(index, "First Name"))
Append(index.Fields, CreateField(index, "Last Name"))
Unique(index) = -1
Append(table.Indexes, index)
Append(newdb.TableDefs, table)
table = CreateTableDef(newdb, "Test Table 2")
Append(table.Fields, CreateField(table, "First Name", constants.dbText))
Append(table.Fields, CreateField(table, "Last Name", constants.dbText))
Append(newdb.TableDefs, table)
relation = CreateRelation(newdb, "TestRelationship")
Table(relation) = "Test Table 1"
ForeignTable(relation) = "Test Table 2"
field = CreateField(relation, "First Name")
ForeignName(field) = "First Name"
Append(relation.Fields, field)
field = CreateField(relation, "Last Name")
ForeignName(field) = "Last Name"
Append(relation.Fields, field)
Attributes(relation) = constants.dbRelationDeleteCascade + constants.dbRelationUpdateCascade
Append(newdb.Relations, relation)
tab1 = OpenRecordset(newdb, "Test Table 1")
AddNew(tab1)
Value(tab1.Fields("First Name")) = "Mark"
Value(tab1.Fields("Last Name")) = "Hammond"
Update(tab1)
MoveFirst(tab1)
bk = Bookmark(tab1)
AddNew(tab1)
Value(tab1.Fields("First Name")) = "Second"
Value(tab1.Fields("Last Name")) = "Person"
Update(tab1)
MoveLast(tab1)
if Value(tab1.Fields("First Name")) != "Second"
throw(RuntimeError("Unexpected record is last - makes bookmark test pointless!"))
end
Bookmark(tab1) = bk
if Bookmark(tab1) != bk
throw(RuntimeError("The bookmark data is not the same"))
end
if Value(tab1.Fields("First Name")) != "Mark"
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
@printf("Opening database %s", dbname)
OpenCurrentDatabase(a, dbname)
db = CurrentDb(a)
DumpDB(daodump, db, 1)
forms = Forms(a)
@printf("There are %d forms open.", length(forms))
reports = Reports(a)
@printf("There are %d reports open", length(reports))
finally
if !(a === nothing)
write(sys.stderr, "Closing database\n")
try
CloseCurrentDatabase(a)
catch exn
if exn isa com_error(pythoncom)
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
write(sys.stderr, "testAccess not doing dynamic test, as generated code already exists\n")
end
DoDumpAccessInfo(dbname)
end

function test(dbname = nothing)
if dbname === nothing
try
GenerateSupport()
catch exn
if exn isa com_error(pythoncom)
println("*** Can not import the MSAccess type libraries - tests skipped")
return
end
end
dbname = CreateTestAccessDatabase()
@printf("A test database at \'%s\' was created", dbname)
end
DumpAccessInfo(dbname)
end

function main()
dbname = nothing
if length(append!([PROGRAM_FILE], ARGS)) > 1
dbname = append!([PROGRAM_FILE], ARGS)[2]
end
test(dbname)
CheckClean()
end

main()
end