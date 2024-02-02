import os
import subprocess

# 要执行的可执行文件路径
executable_path = '/home/liscopye/kecc-public/target/debug/kecc'

# 目标文件夹路径
folder_path = '/home/liscopye/kecc-public/examples/c'

output_folder_path = '/home/liscopye/kecc-public/ir-test'

origin_path = '/home/liscopye/kecc-public/examples/ir0'

ir1_path = '/home/liscopye/kecc-public/examples/ir1'

diff_result_path = '/home/liscopye/kecc-public/ir-cmp'

ir0_pictures_path = '/home/liscopye/kecc-public/ir0-images'
ir1_pictures_path = '/home/liscopye/kecc-public/ir1-images'
# 遍历文件夹
for filename in os.listdir(folder_path):
    # 构建文件的完整路径
    file_path = os.path.join(folder_path, filename)

    # 检查文件是否为普通文件
    if os.path.isfile(file_path):
        # 构建输出文件的路径（.ir 后缀）
        output_path = os.path.join(output_folder_path, os.path.splitext(filename)[0] + '.ir')

        # 构建执行命令
        command = [executable_path, '-i', file_path]

        # 使用 subprocess 执行命令，并将输出重定向到 .ir 文件
        with open(output_path, 'w') as output_file:
            subprocess.run(command, stdout=output_file, stderr=output_file)


        

# 遍历文件夹
for filename in os.listdir(output_folder_path):
    # 构建文件的完整路径
    file_path1 = os.path.join(output_folder_path, filename)
    file_path2 = os.path.join(origin_path, filename)

    # 检查文件是否为普通文件
    if os.path.isfile(file_path):
        # 构建输出文件的路径（.ir 后缀）
        output_path = os.path.join(diff_result_path, os.path.splitext(filename)[0] + '.cmp')

        # 构建执行命令
        command = ['diff', file_path1, file_path2]

        # 使用 subprocess 执行命令，并将输出重定向到 .ir 文件
        with open(output_path, 'w') as output_file:
            subprocess.run(command, stdout=output_file, stderr=output_file)


# 遍历文件夹
list = ['complete_cond.ir', 'float2.ir']
for filename in os.listdir(origin_path):
    # 构建文件的完整路径
    file_path = os.path.join(origin_path, filename)
    if filename in list :
        continue
    # 检查文件是否为普通文件
    if os.path.isfile(file_path):
        # 构建输出文件的路径（.ir 后缀）
        output_file = os.path.splitext(filename)[0] + '.png'

        # 构建执行命令
        command = [executable_path, '--irviz', output_file, file_path]

        subprocess.run(command)

        command = ['mv' ,output_file, ir0_pictures_path]

        subprocess.run(command)

# 遍历文件夹
for filename in os.listdir(ir1_path):
    # 构建文件的完整路径
    file_path = os.path.join(ir1_path, filename)
    if filename in list :
        continue
    # 检查文件是否为普通文件
    if os.path.isfile(file_path):
        # 构建输出文件的路径（.ir 后缀）
        output_file = os.path.splitext(filename)[0] + '.png'

        # 构建执行命令
        command = [executable_path, '--irviz', output_file, file_path]

        subprocess.run(command)

        command = ['mv' ,output_file, ir1_pictures_path]

        subprocess.run(command)
