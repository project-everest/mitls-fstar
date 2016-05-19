#!/bin/bash

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo /etc/init.d/postgresql stop;
  for d in mysql ; do
    sudo rm -rf /var/lib/$d
    sudo mv /var/ramfs/$d /var/lib/
    sudo ln -s /var/lib/$d /var/ramfs/$d
  done
  free -h;
fi
