import MySQLdb

def connect():
    return MySQLdb.connect(
        user="dev",
        passwd="blargh",
        host="localhost",
        db="dev_cornerhost")
