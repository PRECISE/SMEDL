import lldb
import os
import re
import sys, getopt

instsList = ["addl", "cmpl","movl"]

def disassemble_instructions(insts,val):
    for i in insts:
        if str(i).find(val) != -1:
            for item in instsList:
                if str(i).find(item) != -1:
                    ot = re.findall('\$+', str(i))
                    if ot:
                        final = re.search(r"\[([A-Za-z0-9_]+)\]", str(i))
                        print final.group(1)

def command_interpreter(binary_file,cmd_args):
        arguments = cmd_args[0].split(",")
        for arg in arguments:
            print arg
            if arg.rfind(".") == -1:
                func_name = arg
                decode_command(binary_file,func_name,False)
            else:
                #print arg
                func_name = arg.split(".")[0]
                #print func_name
                param = arg.split(".")[1:]
                for par in param:
                    var = par
                    print var
                    decode_command(binary_file,func_name,var)
        #3else:
         #       print "usage: cmd.py <binary_file> <function_name,function_name:variable>"
                #sys.exit()

def decode_command(binary_file,func_name,var):

        exe = os.path.join(os.getcwd(),binary_file)

        dbg = lldb.SBDebugger.Create()

        # Create a target by the debugger.
        target = dbg.CreateTarget(exe)

        dbg.SetAsync(False)

        target.BreakpointCreateByName (func_name,target.GetExecutable().GetFilename());

        # Retrieve the associated command interpreter from our debugger.
        ci = dbg.GetCommandInterpreter()
        res = lldb.SBCommandReturnObject()

        ci.HandleCommand('process launch', res)
        process = ci.GetProcess()

        state = process.GetState()
        if state == lldb.eStateStopped:
            thread = process.GetThreadAtIndex(0)
            if thread:
                frame = thread.GetFrameAtIndex(0)
                if frame:
                    function = frame.GetFunction()
                    addr = function.GetStartAddress()
                    start_addr = hex(int(addr.GetFileAddress()))
                    print start_addr
                    if var:

                        str1 = 'image lookup --address'
                        str1 += " " + start_addr + " " + '--verbose'
                        varStr = 'name = '
                        varStr += '"' + var + '"'

                        ci.HandleCommand(str1, res)
                        #print res
                        outs = str(res).split("\n")
                        for out in outs:
                            if out.find("Variable") != -1 and out.find(varStr) != -1:
                                element =  out.split(",")
                                for ele in element:
                                    if ele.find("location") != -1:
                                        m = re.search(r"(\d+)", ele)
                                        hexStr = hex(int(m.group()))
                                        print hexStr

                                        if hexStr:
                                            insts = function.GetInstructions(target)
                                            disassemble_instructions(insts,hexStr)



if __name__=='__main__':
    binary_file = sys.argv[1]
    command_interpreter(binary_file,sys.argv[2:])

