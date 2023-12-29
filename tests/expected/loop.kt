fun for_with_break() {
    for (i in (0..4 - 1)) {
        if (i == 2) {
            break
        }
        println("$i")
    }
}

fun for_with_continue() {
    for (i in (0..4 - 1)) {
        if (i == 2) {
            continue
        }
        println("$i")
    }
}

fun for_with_else() {
    val has_break = false
    for (i in (0..4 - 1)) {
        println("$i")
    }
    if (has_break != true) {
        println("OK")
    }
}

fun while_with_break() {
    var i = 0
    while (true) {
        if (i == 2) {
            break
        }
        println("$i")
        i += 1
    }
}

fun while_with_continue() {
    var i = 0
    while (i < 5) {
        i += 1
        if (i == 2) {
            continue
        }
        println("$i")
    }
}

fun main(argv: Array<String>) {
    for_with_break()
    for_with_continue()
    for_with_else()
    while_with_break()
    while_with_continue()
}
