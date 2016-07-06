/* conditions of the GrammaTech SySense End-User License Agreement^M */
/* Version 2014-03 (effective date 2016/04/06) entered into between^M */
/* GrammaTech and The Trustees of the University of Pennsylvania.^M */
/* Distribution without the express written consent of an authorized^M */
/* representative of GrammaTech.  GrammaTech disclaims any and all^M */
/* warranty and liability arising from or related to use of this software^M */
/* or information.^M */
/* ^M */
/* (c) GrammaTech, Inc. 2014-2016.  All rights reserved.^M */
/* ^M */

#include "api/sysense_types.h"
#include "api/client_c_api.h"
#include "api/client_clib.h"
#include "api/invariant_monitor_client.h"
#include "{{header_file}}"

monitor_id {{monitor_id }};

{% for item in list_item %}

void {{item['func_name']}}_ivm_action(void *esp,void *user_info){

    unsigned int *info = (unsigned int *)esp;

     sysense_printf ("Ivm_action:{{item['func_name']}} .\n");
    
}
{%- endfor %}

void ivm_on_new_process(monitor_id id, invariant_mon_event *ivmevent){

    
    char app_to_monitor[] = "./{{file_name }}";   
  
     
    if(s_strcmp(ivmevent->arg0, app_to_monitor) ==0) {

        CheckExprID c_one  = Expr_Constant(1);
        CheckExprID c_zero = Expr_Constant(0);
        CheckExprID expr = Expr_BinaryOp(GT_OP,c_zero,c_one);

        {% for input in list_item %} 
            

         InstructionBlockReference {{input['func_name']}}_iblock =
                    CreateInvariantCheck(expr,{{input['func_name']}}_ivm_action,(void*)0xBADCAD);

         unsigned int check_id_{{input['func_name']}} = InsertCheck(id,ivmevent->gid,{{input['func_name'] }}_iblock);
            {% for values in input['check_addr'] %}

         void *checkAddr_{{input['func_name']}}{{input['check_addr'].index(values)}} = (void *){{values}};

         EnableCheck(id, ivmevent->gid,checkAddr_{{input['func_name']}}{{input['check_addr'].index(values)}}, check_id_{{input['func_name']}});
            {%- endfor %}
                        
    {%- endfor %}       
    
        
    }    


}


void invariant_agent(void)
{
    sysense_printf("Invariant Monitoring Agent: Sysense version=%s\n", get_version());

    // Grab the handle for the syscall monitor, if present
    {{monitor_id }} = get_monitor_id("Invariant");
    if ({{monitor_id }} == NULL) {
        sysense_printf("Invariant Monitoring Agent: Invariant monitor not present. Exiting.\n");
        return;
    }

    // Configure and listen to the invariant monitor
    monitor_config config;
    config.request_level = 3;
    configure_monitor({{monitor_id }}, &config);
    enable_monitor({{monitor_id }});
    listen_to_monitor({{monitor_id }}, &config);

    while (1) {
        event_notification event;
        receive_event(&event);
        switch (event.type) {
            case IVM_EVENT_NEW_PROCESS:
            case IVM_EVENT_NEW_PROCESS_NAME:
                {
                invariant_mon_event *evt = (invariant_mon_event *)event.info;
                ivm_on_new_process({{monitor_id }},evt);
                }
                break;
            case IVM_EVENT_PROCESS_DEAD:
                {
                }
                break;
            case IVM_EVENT_PROCESS_FORGOTTEN:
                {
                }
                break;
            default:
                sysense_printf ("Invariant Monitor client : Unknown event %X. Ignoring\n",event.type);
                break;
       }

    }















}
