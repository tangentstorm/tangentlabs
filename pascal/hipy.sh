rm -f HelloPy.so
fpc -gl -B -Xc HelloPy.pas \
&& mv ./libHelloPy.so HelloPy.so \
&& python hellopas.py
