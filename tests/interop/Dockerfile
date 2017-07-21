# Use an official Python runtime as a parent image
FROM python:3.6.1

# Set the working directory to /tls-tests
WORKDIR /tls-tests

# Copy the current directory contents into the container at /app
COPY mitls_tester.py 		/tls-tests
COPY docker_config.py 		/tls-tests/config.py
COPY tlsparser.py 			/tls-tests
COPY openssl.py 			/tls-tests
COPY output_redirector.py 	/tls-tests/
COPY dependencies 			/tls-tests/
COPY cutils/cutils.so 		/tls-tests/cutils/

# Install any needed packages specified in requirements.txt
# RUN pip install -r requirements.txt
RUN pip3 install cryptography
RUN apt-get update
RUN apt-get --assume-yes install vim

# Make port 80 available to the world outside this container
# EXPOSE 80

# Define environment variable
# ENV NAME World

# Run app.py when the container launches
# CMD ["python", "app.py"]
# CMD ["/bin/bash"]