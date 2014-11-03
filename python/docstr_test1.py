# compare with docstr_test0
"""docstring"""         # this should get asssigned to docstr_test1.__doc__
# comment 0             # pyc for this file should be much smaller since
# comment 1             # these are not docstrings. (which means less bytecode
                        # and less wasted action at runtime)
