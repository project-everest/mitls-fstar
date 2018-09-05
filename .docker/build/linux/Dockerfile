# miTLS build container

# Define on fstar-version.json what FStar base container image
# mitls build should use.
# By default it always look for the latest FStar container available
# In case you would like to reference a specific commit,
# replace latest with the commit id from github using 12 characters.
ARG COMMITID
FROM fstar-linux:${COMMITID}

ARG BUILDLOGFILE
ARG MAXTHREADS
ARG TARGET
ARG BRANCHNAME
ARG FSTARSOURCEVERSION

WORKDIR ${MYHOME}/FStar

# Do some cleanup
RUN rm -rf hacl-star
RUN rm -rf hacl-star-old
RUN rm -rf kremlin
RUN rm -rf hacl-star
RUN rm -rf mitls-fstar
RUN rm -rf vale

RUN rm -f build.sh
RUN rm -f build_helper.sh
RUN rm -f buildlogfile.txt
RUN rm -f log_no_replay.html
RUN rm -f log_worst.html
RUN rm -f orange_status.txt
RUN rm -f result.txt
RUN rm -f status.txt
RUN rm -f commitinfofilename.json

RUN mkdir ${MYHOME}/FStar/mitls-fstar
COPY --chown=everest / ${MYHOME}/FStar/mitls-fstar/

# Do another cleanup
RUN rm ${MYHOME}/FStar/mitls-fstar/Dockerfile
RUN rm ${MYHOME}/FStar/mitls-fstar/build.sh
RUN rm ${MYHOME}/FStar/mitls-fstar/build_helper.sh
RUN rm ${MYHOME}/FStar/mitls-fstar/id_rsa
RUN rm ${MYHOME}/FStar/mitls-fstar/commitinfofilename.json

# ADD SSH KEY
RUN mkdir -p ${MYHOME}/.ssh
RUN chown everest ${MYHOME}/.ssh
RUN chmod 700 ${MYHOME}/.ssh
COPY --chown=everest id_rsa ${MYHOME}/.ssh/id_rsa
RUN chmod 600 ${MYHOME}/.ssh/id_rsa

COPY --chown=everest build.sh ${MYHOME}/FStar/build.sh
RUN chmod +x build.sh
COPY --chown=everest build_helper.sh ${MYHOME}/FStar/build_helper.sh
RUN chmod +x build_helper.sh

RUN ./build_helper.sh ${TARGET} ${BUILDLOGFILE} ${MAXTHREADS} ${BRANCHNAME} ${FSTARSOURCEVERSION} || true

# Remove ssh identities.
RUN rm ${MYHOME}/.ssh/id_rsa