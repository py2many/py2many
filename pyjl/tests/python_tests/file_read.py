class C1:
    def file_reader(file_name:str):
        for file_row in open(file_name, "r"):
            yield file_row

class C2:
    def file_reader(file_name:str):
        file = open(file_name, "r")
        while data := file.read(64):
            yield data

if __name__ == "__main__":
    c1_file_reader = C1.file_reader("C:/Users/Miguel Marcelino/Desktop/test.txt")
    c2_file_reader = C2.file_reader("C:/Users/Miguel Marcelino/Desktop/test.txt")

    for data in c1_file_reader:
        print(data)

    print("--------------------------------------------------------")

    for data2 in c2_file_reader:
        print(data2)

