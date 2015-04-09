from subprocess import call

cmd = ["../c/bin/explorer"]

cmd.append(str(5))
cmd.append(str(4))

for i in range(0, 200):
 cmd.append(str(i))

call(cmd)
