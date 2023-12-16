import matplotlib.pyplot as plt

def main() :
    attr = {'__getitem__': {'Complex': 493,
                 'None': 2379,
                 'bool': 949,
                 'float': 65,
                 'int': 112,
                 'list': 173,
                 'set': 5,
                 'str': 474,
                 'tuple': 65},
 '__iter__': {'Complex': 241,
              'None': 1097,
              'Union': 272,
              'bool': 71,
              'float': 18,
              'int': 81},
 '__setitem__': {'Complex': 123,
                 'None': 188,
                 'bool': 48,
                 'bytes': 5,
                 'dict': 13,
                 'float': 20,
                 'int': 18,
                 'set': 7,
                 'str': 79,
                 'tuple': 43}}

    operator = {'Complex': 559,
 'None': 1366,
 'Union': 498,
 'bool': 13,
 'bytes': 63,
 'dict': 26,
 'float': 76,
 'int': 328,
 'list': 236,
 'str': 330,
 'tuple': 82}

    # draw pie chart of operator
    plt.pie(
        operator.values(),
        labels=operator.keys(),
        autopct="%.1f%%"
    )

    plt.title("Operator")
    plt.show()

if __name__ == "__main__":
    main()