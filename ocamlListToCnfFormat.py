import sys


def main():
    inp = input("ocaml list: ")
    l = eval(inp.replace(";", ","))
    litterals = []
    out = ""
    for subl in l:
        for litt in subl:
            if not abs(litt) in litterals:
                litterals.append(abs(litt))
            out += "%d "%litt
        out += "0\n"

    print("p cnf %d %d\n"%(len(litterals), len(l)))
    print(out)




if __name__ == '__main__':
    main()
