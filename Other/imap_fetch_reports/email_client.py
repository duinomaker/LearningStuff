from dataclasses import dataclass
import tempfile
import email
from email.parser import Parser
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from imaplib import IMAP4_SSL
from smtplib import SMTP_SSL

import utils


class IMAPError(BaseException):
    pass


@dataclass(frozen=True)
class NamedTemporaryFile:
    raw_name: str
    path: str


@dataclass(frozen=True)
class EMailAttachment:
    timestamp: int
    sender: str
    tmp_file: NamedTemporaryFile


class EMailClient:
    def __init__(self):
        self.logged_in = False

    @classmethod
    def from_config(cls, config):
        account = config.account
        client = EMailClient()
        client.login(account['imap'], account['smtp'],
                     account['user'], account['password'])
        return client

    def login(self, server_imap, server_smtp, user, password):
        assert not self.logged_in
        self.address = user
        self.imap = IMAP4_SSL(server_imap)
        self.imap.login(user=user, password=password)
        self.smtp = SMTP_SSL(server_smtp)
        self.smtp.login(user=user, password=password)
        self.logged_in = True

    def logout(self):
        assert self.logged_in
        self.imap.logout()
        self.smtp.close()
        self.logged_in = False

    def send_text(self, receivers, subject, content='', charset='utf-8'):
        message = MIMEMultipart()
        message['From'] = self.address
        message['To'] = ', '.join(receivers)
        message['Subject'] = subject
        message.attach(MIMEText(content, _charset=charset))
        self.smtp.sendmail(self.address, receivers, message.as_string())

    def fetch_attachments(self, mailbox='INBOX'):
        assert self.logged_in
        resp, msgs = self.imap.select(mailbox=mailbox)
        if resp != 'OK':
            raise IMAPError(b'\n'.join(msgs).decode())

        resp, nums = self.imap.search(None, 'ALL')
        if resp != 'OK':
            raise IMAPError('Failed to search mailbox')

        attachments = []
        for num in nums[0].split():
            resp, data = self.imap.fetch(num, '(RFC822)')
            if resp != 'OK':
                RuntimeError('IMAP: Failed to fetch mails')
            raw_email_string = data[0][1].decode()
            email_message = email.message_from_string(raw_email_string)
            headers = Parser().parsestr(raw_email_string)
            timestamp = utils.extract_timestamp(headers['Date'])
            sender = utils.extract_address(headers['From'])

            # Get attachments and parse
            for data in email_message.walk():
                if data.get('Content-Disposition') is None \
                        or data.is_multipart():
                    continue
                file_name = data.get_filename()
                if file_name is None:
                    continue
                file_name = utils.decode_mime(file_name)
                _, tmp_path = tempfile.mkstemp()
                with open(tmp_path, 'wb') as fp:
                    fp.write(data.get_payload(decode=True))
                tmp_file = NamedTemporaryFile(raw_name=file_name,
                                              path=tmp_path)
                attachments.append(EMailAttachment(timestamp=timestamp,
                                                   sender=sender,
                                                   tmp_file=tmp_file))
            self.imap.store(num, '+FLAGS', r'\SEEN')
        self.imap.close()
        return attachments
