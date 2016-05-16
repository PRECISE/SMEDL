from subprocess import call
from random import randint

cmd = ["./explorer_mon"]

for i in range(0,2):
    cmd.append(str(randint(0, 9)))
    cmd.append(str(randint(0, 19)))

    map = [str(0)] * 200
    for i in range(0, 10):
        map[randint(0, 199)] = str(-1)
    index=[]
    i = 0
    while i < 5 :
        k = randint(0,199)
        if k in index:
            continue
        i = i + 1
        index.append(k)
        map[k] = str(1)
    cmd = cmd + map

call(cmd)
