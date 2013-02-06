@echo off

fpc PyApi.pas
fpc -WR HelloPy
mv -f HelloPy.dll HelloPy.pyd
echo ""
echo "------------------------------"
echo ""

python hellopas.py


