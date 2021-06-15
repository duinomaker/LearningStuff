import os.path
from dataclasses import dataclass


@dataclass(frozen=True)
class ReportInfo:
    type: str
    serial_number: int


@dataclass(frozen=True)
class Report:
    student_id: str
    report_info: ReportInfo


def classify_by_file_name(file_name, config):
    def extract_type(file_name):
        mapping = config.rules
        keys = mapping.keys()
        hit = None
        for k in keys:
            for v in mapping[k]:
                if v in file_name:
                    if hit is not None:
                        return None
                    hit = k
                    break
        return hit

    def extract_serial_number(file_name):
        mapping = {'1': 1, '一': 1, '壹': 1,
                   '2': 2, '二': 2, '贰': 2, '貳': 2,
                   '3': 3, '三': 3, '叁': 3, '參': 3,
                   '4': 4, '四': 4, '肆': 4,
                   '5': 5, '五': 5, '伍': 5,
                   '6': 6, '六': 6, '陆': 6, '陸': 6,
                   '7': 7, '七': 7, '柒': 7,
                   '8': 8, '八': 8, '捌': 8,
                   '9': 9, '九': 9, '玖': 9}
        ordinals = [ch for ch in file_name if ch in mapping.keys()]
        if len(ordinals) != 1:
            return None
        return mapping[ordinals[0]]

    type = extract_type(file_name)
    serial_number = extract_serial_number(file_name)

    if type is None or serial_number is None:
        return None
    return ReportInfo(type=type, serial_number=serial_number)


def is_sender_student(attachment, config):
    return attachment.sender in config.students.keys()


def place_of_belonging(attachment, config):
    report_info = classify_by_file_name(attachment.tmp_file.raw_name, config)
    base_dir = config.paths['reports_dir']

    def is_report_valid():
        return report_info is not None \
               and attachment.sender not in config.exceptions[report_info.type] \
               and report_info.serial_number <= config.latest_nums[report_info.type]

    def directory_name():
        name_mapping = config.names
        # number_mapping = {1: '一', 2: '二', 3: '三', 4: '四', 5: '五',
        #                   6: '六', 7: '七', 8: '八', 9: '九'}
        return '{}#{}'.format(name_mapping[report_info.type],
                              report_info.serial_number)

    def file_name():
        address_mapping = config.students
        student = address_mapping[attachment.sender]
        suffix = os.path.splitext(attachment.tmp_file.raw_name)[1]
        return student.id + student.name + suffix

    if not is_report_valid():
        return None, None
    
    report = Report(student_id=config.students[attachment.sender].id,
                    report_info=report_info)
    return report, os.path.join(base_dir, directory_name(), file_name())
