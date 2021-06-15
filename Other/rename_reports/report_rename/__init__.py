import argparse
import os
import pandas
import re

dirname = os.path.dirname(__file__)


def read_roster():
    mapping = {}
    data = pandas.read_excel(os.path.join(dirname, 'roster.xlsx'),
                             header=None).values
    for student_id, name in data:
        mapping[student_id.strip()] = name.strip()
    return mapping


def batch_rename(directory, suffix, roster):
    def is_document(path):
        if not os.path.isfile(path):
            return False
        ext = os.path.splitext(path)[1].lower()
        return ext in ('.docx', '.doc', '.pdf')

    def extract_student_id(text):
        match = re.search(r'[BbQq][0-9]{8}(?![0-9])', text)
        if match is None:
            return None
        return match.group().upper()

    def renamed_file_path(file_path):
        directory, name = os.path.split(file_path)
        _, ext = os.path.splitext(name)
        return os.path.join(directory,
                            suffix % (student_id, roster[student_id]) + ext)

    if not os.path.exists(directory):
        raise RuntimeError('no such file or directory: {}'.format(directory))
    if not os.path.isdir(directory):
        raise RuntimeError('not a directory: {}'.format(directory))

    tally = {k: False for k in roster.keys()}
    file_paths = [os.path.join(directory, f) for f in os.listdir(directory)]
    file_paths = filter(is_document, file_paths)
    mapping = []
    for file_path in file_paths:
        _, file_name = os.path.split(file_path)
        student_id = extract_student_id(file_name)
        if student_id is None or student_id not in roster.keys():
            raise RuntimeError("no valid student ID found in filename: '{}'"
                               .format(file_name))
        if tally[student_id]:
            raise RuntimeError('multiple files under a single student ID: {}'
                               .format(student_id))
        if roster[student_id] not in file_name:
            raise RuntimeError("student's name '{}' not found in filename: {}"
                               .format(roster[student_id], file_name))
        tally[student_id] = True
        mapping.append((file_path, renamed_file_path(file_path)))
    for file_from, file_to in mapping:
        os.rename(file_from, file_to)
    return [student_id for student_id, submitted in tally.items() if submitted]
