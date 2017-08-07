# Use an official Python runtime as a parent image
FROM python:3.6.1

# Set the working directory to /tls-tests
WORKDIR /tls-tests

# Copy the current directory contents into the container at /app
COPY mitls_tester.py 			/tls-tests
COPY docker_config.py 			/tls-tests/config.py
COPY tlsparser.py 				/tls-tests
COPY docker_nss.py 				/tls-tests/nss.py
COPY nss_tester.py 				/tls-tests
COPY pr_wrapper.py 				/tls-tests
COPY interoperability_tester.py /tls-tests
COPY cutils.py 					/tls-tests
COPY openssl.py 				/tls-tests
COPY openssl_tester.py 			/tls-tests
COPY bio_wrapper.py 			/tls-tests
COPY output_redirector.py 		/tls-tests/
COPY dependencies 				/tls-tests/
COPY certificates/ecdsa/        /tls-tests/certificates/ecdsa/
COPY cutils/cutils.so 			/tls-tests/cutils/

# Install any needed packages specified in requirements.txt
RUN pip3 install cryptography
RUN apt-get update
RUN apt-get --assume-yes install vim

# Make port 80 available to the world outside this container
# EXPOSE 80

# Define environment variable
# ENV NAME World
ENV LD_LIBRARY_PATH nss-dependencies/:openssl-dependencies/

# Run app.py when the container launches
# CMD ["python", "app.py"]
# CMD ["/bin/bash"]