import re
import time
import base64
import quopri
import configparser
from dataclasses import dataclass
from email.utils import parsedate, parseaddr


@dataclass(frozen=True)
class Student:
    id: str
    name: str


def student_from_tuple(id, name):
    return Student(id=id, name=name)


@dataclass(frozen=True)
class Config:
    account: dict
    rules: dict
    names: dict
    latest_nums: dict
    students: dict
    exceptions: dict
    paths: dict


def read_config(file_path, account_field, type_mapping_field,
                name_mapping_field, latest_mapping_field,
                students_field, exceptions_field,
                paths_field):
    parser = configparser.ConfigParser()
    parser.read(file_path)

    account = parser[account_field]
    account = {k: account.get(k) for k in account.keys()}

    rules = parser[type_mapping_field]
    rules = {k: rules.get(k).split() for k in rules.keys()}

    names = parser[name_mapping_field]
    names = {k: names.get(k) for k in names.keys()}

    latest_nums = parser[latest_mapping_field]
    latest_nums = {k: int(latest_nums.get(k)) for k in latest_nums.keys()}

    students = parser[students_field]
    students = {k: student_from_tuple(*students.get(k).split())
                for k in students.keys()}

    exceptions = parser[exceptions_field]
    exceptions = {k: exceptions.get(k).split() for k in exceptions.keys()}

    paths = parser[paths_field]
    paths = {k: paths.get(k) for k in paths.keys()}

    return Config(account=account,
                  rules=rules,
                  names=names,
                  latest_nums=latest_nums,
                  students=students,
                  exceptions=exceptions,
                  paths=paths)


def decode_mime(text):
    matched = re.match(r'=\?([^?]+)\?([BQ])\?(.+?)\?=', text)
    content_encoding, encoding, content = matched.groups()
    if encoding == 'B':
        return base64.b64decode(content) \
            .decode(content_encoding)
    if encoding == 'Q':
        return quopri.decodestring(content) \
            .decode(content_encoding)


def extract_address(text):
    return parseaddr(text)[1]


def extract_timestamp(text):
    return int(time.mktime(parsedate(text)))
