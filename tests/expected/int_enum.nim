
type Colors = enum
    RED,
    GREEN,
    BLUE,


type
    Permissions = enum
        R = 1,
        W = 2,
        X = 16,
    PermissionsFlags = set[Permissions]

