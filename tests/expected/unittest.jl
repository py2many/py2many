import unittest
struct UnitTestTranslation

end

function testSequences(self::UnitTestTranslation)
    x = [1, 2]
    z = x
    assertEqual(self, z, [1, 2])
    x = [1, 2, 3]
    y = x
    assertTrue(self)
end

function main()
    unit_test_translation = UnitTestTranslation()
    testSequences(unit_test_translation)
end

main()
