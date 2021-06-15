import os

from reports import is_sender_student, place_of_belonging
from utils import read_config
from email_client import EMailClient
from index import Index

if __name__ == '__main__':
    config = read_config('config.ini', 'ACCOUNT', 'RULE',
                         'NAMING', 'LATEST',
                         'STUDENTS', 'EXCEPTIONS',
                         'PATHS')
    client = EMailClient.from_config(config)
    index = Index.from_config(config)

    attachments = client.fetch_attachments()
    for attachment in attachments:
        if not is_sender_student(attachment, config):
            os.unlink(attachment.tmp_file.path)
            continue
        report, path = place_of_belonging(attachment, config)
        if path is None:
            # message = '系统无法识别文件名 “{}”\n\n请确保文件名包含正确的课程名称、实验序号，' \
            #           '例如 “数据结构3.docx” 或 “密码学二.doc”。' \
            #     .format(attachment.tmp_file.raw_name)
            # client.send_text([attachment.sender], '系统提示', message)
            print('Failed to read "{}"'.format(attachment.tmp_file.raw_name))
            os.unlink(attachment.tmp_file.path)
            continue
        if not index.exists(report) \
                or index.is_report_newer(report, attachment.timestamp):
            if os.path.exists(path):
                os.unlink(path)
            containing_dir = os.path.split(path)[0]
            if not os.path.exists(containing_dir):
                os.makedirs(containing_dir)
            os.rename(attachment.tmp_file.path, path)
            index.update(report, attachment.timestamp)

    index.save(config)
    client.logout()
