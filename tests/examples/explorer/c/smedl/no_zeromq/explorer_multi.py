from subprocess import call
from random import randint

cmd = ["./multi_mac"]

for i in range(0,125):
    cmd.append(str(randint(0, 9)))
    cmd.append(str(randint(0, 19)))

    map = [str(0)] * 200
    for i in range(0, 10):
        map[randint(0, 199)] = str(-1)
    for i in range(0, 10):
        map[randint(0, 199)] = str(1)
    cmd = cmd + map
call(cmd)