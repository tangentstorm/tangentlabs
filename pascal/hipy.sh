rm -f HelloPy.so
fpc -gl -B -Xc HelloPy.pas \
&& mv gen/libHelloPy.so HelloPy.so \
&& python hellopas.py
