import tables
proc show() =
  var my_list = @[1, 2, 3, 4, 5]
  # del unimplemented on line 7:4

  echo len(my_list)
  var my_dict = {"a": 1, "b": 2, "c": 3}.newTable
  # del unimplemented on line 12:4

  echo len(my_dict)

proc main() =
  show()

main()
