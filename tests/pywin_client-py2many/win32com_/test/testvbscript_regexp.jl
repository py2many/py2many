module testvbscript_regexp

using win32com.client.gencache: EnsureDispatch
using win32com.client.dynamic: DumbDispatch
import win32com.test.util
abstract type AbstractRegexTest <: Abstractwin32com.test.util.TestCase end
mutable struct RegexTest <: AbstractRegexTest

end
function _CheckMatches(self::RegexTest, match, expected)
found = []
for imatch in match
append(found, FirstIndex(imatch))
end
assertEqual(self, collect(found), collect(expected))
end

function _TestVBScriptRegex(self::RegexTest, re)
StringToSearch = "Python python pYthon Python"
Pattern(re) = "Python"
Global(re) = true
IgnoreCase(re) = true
match = Execute(re, StringToSearch)
expected = (0, 7, 14, 21)
_CheckMatches(self, match, expected)
IgnoreCase(re) = false
match = Execute(re, StringToSearch)
expected = (0, 21)
_CheckMatches(self, match, expected)
end

function testDynamic(self::RegexTest)
re = DumbDispatch("VBScript.Regexp")
_TestVBScriptRegex(self, re)
end

function testGenerated(self::RegexTest)
re = EnsureDispatch("VBScript.Regexp")
_TestVBScriptRegex(self, re)
end

function main()

end

main()
end