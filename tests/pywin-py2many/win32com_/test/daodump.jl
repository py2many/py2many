using Printf

import win32com_.client
function DumpDB(db, bDeep = 1)
    DumpTables(db, bDeep)
    DumpRelations(db, bDeep)
    DumpAllContainers(db, bDeep)
end

function DumpTables(db, bDeep = 1)
    for tab in db.TableDefs
        tab = TableDefs(db, tab.Name)
        @printf(
            "Table %s - Fields: %d, Attributes:%d\n",
            tab.Name,
            length(tab.Fields),
            tab.Attributes
        )
        if bDeep
            DumpFields(tab.Fields)
        end
    end
end

function DumpFields(fields)
    for field in fields
        @printf(
            "  %s, size=%d, reqd=%d, type=%d, defVal=%s\n",
            field.Name,
            field.Size,
            field.Required,
            field.Type,
            string(field.DefaultValue)
        )
    end
end

function DumpRelations(db, bDeep = 1)
    for relation in db.Relations
        @printf(
            "Relation %s - %s->%s\n",
            relation.Name,
            relation.Table,
            relation.ForeignTable
        )
    end
end

function DumpAllContainers(db, bDeep = 1)
    for cont in db.Containers
        @printf("Container %s - %d documents\n", cont.Name, length(cont.Documents))
        if bDeep
            DumpContainerDocuments(cont)
        end
    end
end

function DumpContainerDocuments(container)
    for doc in container.Documents
        timeStr = ctime(time, parse(Int, doc.LastUpdated))
        print("$(doc.Name) - updated $(timeStr)")
        println("$(doc.LastUpdated))")
    end
end

function TestEngine(engine)
    if length(append!([PROGRAM_FILE], ARGS)) > 1
        dbName = append!([PROGRAM_FILE], ARGS)[2]
    else
        dbName = "e:\\temp\\TestPython.mdb"
    end
    db = OpenDatabase(engine, dbName)
    DumpDB(db)
end

function test()
    for progid in ("DAO.DBEngine.36", "DAO.DBEngine.35", "DAO.DBEngine.30")
        try
            ob = EnsureDispatch(win32com_.client.gencache, progid)
        catch exn
            if exn isa pythoncom.com_error
                println("$(progid)does not seem to be installed")
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    test()
end
