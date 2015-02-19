from subprocess import call

cmd = ["./explorer"]

for i in range(0, 100):
 cmd.append(str(i))

call(cmd)
