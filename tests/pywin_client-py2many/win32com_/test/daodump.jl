module daodump
using Printf


import win32com.client
function DumpDB(db, bDeep = 1)
    DumpTables(db, bDeep)
    DumpRelations(db, bDeep)
    DumpAllContainers(db, bDeep)
end

function DumpTables(db, bDeep = 1)
    for tab in TableDefs(db)
        tab = TableDefs(db, Name(tab))
        @printf(
            "Table %s - Fields: %d, Attributes:%d",
            (Name(tab), length(Fields(tab)), Attributes(tab))
        )
        if bDeep
            DumpFields(Fields(tab))
        end
    end
end

function DumpFields(fields)
    for field in fields
        @printf(
            "  %s, size=%d, reqd=%d, type=%d, defVal=%s",
            (
                Name(field),
                Size(field),
                Required(field),
                Type(field),
                string(DefaultValue(field)),
            )
        )
    end
end

function DumpRelations(db, bDeep = 1)
    for relation in Relations(db)
        @printf(
            "Relation %s - %s->%s",
            (Name(relation), Table(relation), ForeignTable(relation))
        )
    end
end

function DumpAllContainers(db, bDeep = 1)
    for cont in Containers(db)
        @printf("Container %s - %d documents", (Name(cont), length(Documents(cont))))
        if bDeep
            DumpContainerDocuments(cont)
        end
    end
end

function DumpContainerDocuments(container)
    for doc in Documents(container)
        timeStr = ctime(time, parse(Int, LastUpdated(doc)))

        println(LastUpdated(doc), ")")
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
            ob = EnsureDispatch(win32com.client.gencache, progid)
        catch exn
            if exn isa com_error(pythoncom)
                println(progid, "does not seem to be installed")
            end
        end
    end
end

function main()
    test()
end

main()
end
