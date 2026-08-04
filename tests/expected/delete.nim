import tables
proc show() =
  var my_list = @[1, 2, 3, 4, 5]
  my_list.delete(2)
  echo len(my_list)
  var my_dict = {"a": 1, "b": 2, "c": 3}.newTable
  my_dict.del("b")
  echo len(my_dict)

proc main() =
  show()

main()
