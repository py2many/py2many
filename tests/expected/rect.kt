
data class Rectangle(val height: Int, val length: Int) {
    fun is_square(): Boolean {
        return height == length
    }
}
