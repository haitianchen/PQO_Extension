import configparser
import socketserver
import json
import sys
import time
import os
import math
import re
import struct
def read_config():
    config = configparser.ConfigParser()
    config.read("ML.cfg")

    if "ML" not in config:
        print("ML.cfg does not have a [ML] section.")
        exit(-1)

    config = config["ML"]
    return config
def clean_text(input_text):
    # 去除 \n
   # return input_text
    cleaned_text = re.sub(r'\n', '', input_text)
    #cleaned_text = input_text
    # 去除类似 ' ' <repeats ? times> 的文字
    cleaned_text = re.sub(r'"\s*,\s*\' \' <repeats \d+ times>,\s*"', '', cleaned_text)

    return cleaned_text

class JSONTCPHandler(socketserver.BaseRequestHandler):
    def handle(self):
        str_buf = ""
        while True:
            str_buf += self.request.recv(1024).decode("UTF-8")
            if not str_buf:
                # no more data, connection is finished.
                return
            null_loc = str_buf.find("e#nd")
            if null_loc  != -1:
 #               print(str_buf)
                json_msg = str_buf[:null_loc].strip()
                plan_list = json_msg.split('SiGN#')
                json_list = []
                if json_msg:
                    for i in range(len(plan_list)-1):
                        try:
                            json_list.append(json.loads(clean_text(plan_list[i])))
                        except json.decoder.JSONDecodeError:
                            print("Error decoding JSON:", plan_list[i])
                            break
                if self.handle_jsons(json_list):
                    break

def get_plan_order(data):
        #use ML model pick up a plan ,return it's oreder
        print('~~~~'*20)
        print('receive jsons :')
        print(data)
        print('~~~~'*20)
        return 0
class MLJSONHandler(JSONTCPHandler):
    def setup(self):
        self.__messages = []

    def handle_jsons(self, data):
        plan_order = get_plan_order(data)
        self.request.sendall(struct.pack("i", plan_order))
        print('*'*20)
        print('send plan order :',plan_order)
        print('*'*20)
        return True

def start_server(listen_on, port):
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer((listen_on, port), MLJSONHandler) as server:
        server.serve_forever()

if __name__ == "__main__":
    from multiprocessing import Process

    config = read_config()
    port = int(config["Port"])
    listen_on = config["ListenOn"]

    print(f"Listening on {listen_on} port {port}")

    server = Process(target=start_server, args=[listen_on, port])

    print("Spawning server process...")
    server.start()
