import os.path
import pickle


class Index:
    def __init__(self):
        self.mapping = dict()

    @classmethod
    def from_config(cls, config):
        index_file_path = config.paths['index_file']
        if not os.path.exists(index_file_path):
            return Index()
        with open(index_file_path, 'rb') as pkl:
            index = pickle.load(pkl)
        return index

    def exists(self, report):
        return report in self.mapping.keys()

    def is_report_newer(self, report, timestamp):
        assert self.exists(report)
        return timestamp > self.mapping[report]

    def update(self, report, timestamp):
        self.mapping[report] = timestamp

    def save(self, config):
        index_file_path = config.paths['index_file']
        with open(index_file_path, 'wb') as pkl:
            pickle.dump(self, pkl)
