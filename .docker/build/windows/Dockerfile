# Fstar build container
FROM everest_windows_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET

#USER "NT AUTHORITY\SYSTEM"

#BUILD FSTAR
RUN md ${MYHOME}\FStar
COPY / ${MYHOME}/FStar/
WORKDIR ${MYHOME}/FStar

RUN echo %DATE% %TIME% >> %BUILDLOGFILE%
COPY build.sh ${MYHOME}/FStar/build.sh
RUN powershell.exe c:\ewerest\bash.ps1 ./build.sh %TARGET% %BUILDLOGFILE% %MAXTHREADS%

RUN echo %DATE% %TIME% >> %BUILDLOGFILE%

# Generate query-stats.
# List the hints that fail to replay.
RUN powershell.exe c:\ewerest\bash.ps1 .scripts/query-stats.py -f %BUILDLOGFILE% -F html -o log_no_replay.html -n all '--filter=fstar_usedhints=+' '--filter=fstar_tag=-' -g

# Worst offenders (longest times)
RUN powershell.exe c:\ewerest\bash.ps1 .scripts/query-stats.py -f %BUILDLOGFILE% -F html -o log_worst.html -c -g -n 10