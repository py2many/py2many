

fun main_func() {
    var ands: Array<Boolean> = arrayOf()
    var ors: Array<Boolean> = arrayOf()
    var xors: Array<Boolean> = arrayOf()
    for (a in arrayOf(false, true)) {
        for (b in arrayOf(false, true)) {
            ands += a.and(b)
            ors += a.or(b)
            xors += a.xor(b)
        }
    }
    assert(ands == arrayOf(false, false, false, true))
    assert(ors == arrayOf(false, true, true, true))
    assert(xors == arrayOf(false, true, true, false))
    println("OK")
}

fun main(argv: Array<String>) {
    main_func()
}
