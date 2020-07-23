FROM buildpack-deps:focal

ENV LANG C.UTF-8
ENV PY_VERSIONS 3.6 3.7 3.8

# See https://launchpad.net/~deadsnakes/+archive/ubuntu/ppa for key and info
RUN set -eux \
    && apt-get update && apt-get install -y --no-install-recommends gnupg \
    && apt-key adv --keyserver keyserver.ubuntu.com --recv-keys F23C5A6CF475977595C89F51BA6932366A755776 \
    && echo "deb http://ppa.launchpad.net/deadsnakes/ppa/ubuntu focal main" > /etc/apt/sources.list.d/deadsnakes.list \
    && apt-get update \
    && for ver in $PY_VERSIONS; do \
        apt-get install -y python${ver} python${ver}-dev python${ver}-venv; \
    done \
    && apt-get install -y --no-install-recommends python3-pip \
    && apt-get install -y librabbitmq-dev \
    && rm -rf /var/lib/apt/lists/*

CMD ["python3"]
