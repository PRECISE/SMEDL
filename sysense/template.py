import os
from jinja2 import Environment, FileSystemLoader
import string



THIS_DIR = os.path.dirname(os.path.abspath(__file__))

env = Environment(loader=FileSystemLoader(THIS_DIR))
template = env.get_template('object_sysclnt.cpp')


list_item = [{'func_name': 'foo', 'check_addr':['0x80484fb']},{'func_name': 'main_i', 'check_addr': [ '0x804848a','0x80484c5','0x80484cc']}]

output = template.render(list_item=list_item,monitor_id="scm_id",file_name='sample_demo',header_file="ref_client.h")
print output

with open ("sys_demo_client.cpp", 'wb') as fh:
    fh.write(output)
        

