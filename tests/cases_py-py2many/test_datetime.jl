

using test.support.import_helper: import_fresh_module
TESTS = "test.datetimetester"
function load_tests(loader, tests, pattern)
try
pure_tests = import_fresh_module(TESTS, ["datetime", "_strptime"], ["_datetime"])
fast_tests = import_fresh_module(TESTS, ["datetime", "_datetime", "_strptime"])
finally
for modname in ["datetime", "_datetime", "_strptime"]
pop(sys.modules, modname, nothing)
end
end
test_modules = [pure_tests, fast_tests]
test_suffixes = ["_Pure", "_Fast"]
for (module_, suffix) in zip(test_modules, test_suffixes)
test_classes = []
for (name, cls) in items(module.__dict__)
if !isa(cls, type_)
continue;
end
if cls <: unittest.TestCase
push!(test_classes, cls)
elseif cls <: unittest.TestSuite
suit = cls()
append!(test_classes, (type_(test) for test in suit))
end
end
test_classes = sorted(set(test_classes), (cls) -> cls.__qualname__)
for cls in test_classes
cls.__name__ += suffix
cls.__qualname__ += suffix
function setUpClass(cls_, module_ = module_)
cls_._save_sys_modules = copy(sys.modules)
sys.modules[TESTS + 1] = module_
sys.modules["datetime"] = module_.datetime_module
sys.modules["_strptime"] = module_._strptime
end

function tearDownClass(cls_)
clear(sys.modules)
update(sys.modules, cls_._save_sys_modules)
end

cls.setUpClass = setUpClass
cls.tearDownClass = tearDownClass
addTests(tests, loadTestsFromTestCase(loader, cls))
end
end
return tests
end

function main()

end

main()