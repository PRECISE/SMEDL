from subprocess import call

cmd = ["../c/bin/explorer"]

cmd.append(str(5))
cmd.append(str(4))

# TODO: Create randomized input to test out instrumented 'explorer'
for i in range(0, 200):
 cmd.append(str(i))

call(cmd)
