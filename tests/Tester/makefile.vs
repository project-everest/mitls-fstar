CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I.

COMPILE = "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Tools\MSVC\14.15.26726\bin\Hostx64\x64\cl.exe"

LINK = "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Tools\MSVC\14.15.26726\bin\Hostx64\x64\link.exe"

WINLIBDIR = "C:\Program Files (x86)\Windows Kits\10\Lib\10.0.17134.0\um\x64"

all: tester.exe

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
SOURCES = \
  Tester/InteropTester.cpp \
  Tester/Component.cpp \
  Tester/SimpleServer.cpp \
  Tester/Tester.cpp \
  Tester/TLSTester.cpp \
  Tester/stdafx.cpp \
  Tester/mitlsstub.cpp \
  Tester/pngwriter.cpp   

LIBRARIES = \
  Tester/libmipki.lib \
  Tester/libmitls.lib \
  Tester/libquiccrypto.lib
  
OBJECTS = \
  Tester/x64/Debug/InteropTester.obj \
  Tester/x64/Debug/Component.obj \
  Tester/x64/Debug/SimpleServer.obj \
  Tester/x64/Debug/Tester.obj \
  Tester/x64/Debug/TLSTester.obj \
  Tester/x64/Debug/stdafx.obj \
  Tester/x64/Debug/mitlsstub.obj \
  Tester/x64/Debug/pngwriter.obj   
    
tester.exe: 
  $(LINK) -i$(OBJECTS) /MACHINE:X64 /nologo /dll /debug:full /out:tester.exe $(LIBRARIES) $(WINLIBDIR)\ntdll.lib

.cpp.obj::
    $(COMPILE) $(CCOPTS) -c $<

clean:
    -del *.exe
    -del *.obj
