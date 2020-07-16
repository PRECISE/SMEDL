from setuptools import setup, find_packages
# To use a consistent encoding
from codecs import open
from os import path
import json

here = path.abspath(path.dirname(__file__))

# Get the long description from the README file
with open(path.join(here, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()

# Get the package details from the SMEDL about.json file
with open(path.join(here, 'smedl', 'about.json'), encoding='utf-8') as f:
    __about__ = json.load(f)

setup(
    name=__about__['title'],
    version=__about__['version'],
    description=__about__['summary'],
    long_description=long_description,
    url=__about__['uri'],
    author=__about__['author'],
    author_email=__about__['author_email'],
    maintainer=__about__['maintainer'],
    maintainer_email=__about__['maintainer_email'],
    license=__about__['license'],
    classifiers=[
        'Intended Audience :: Developers',
        'Intended Audience :: Science/Research',
        'Programming Language :: Python :: 3',
        'Programming Language :: C',
        'Topic :: Scientific/Engineering',
        'Topic :: Software Development :: Code Generators',
        'Topic :: Software Development :: Quality Assurance',
    ],
    keywords='runtime-verification',

    packages=find_packages(include=['smedl', 'smedl.*']),
    package_data={
        '': ['*.c', '*.h'],
        'smedl': ['about.json'],
        'smedl.parser': ['*.ebnf'],
        'smedl.codegen': ['Makefile', '*.cfg'],
    },

    install_requires=[
        'tatsu>=4.4,<5',
        'Jinja2>=2.10',
        'importlib_resources>=1.1;python_version<"3.7"',
    ],
    python_requires='>=3.6',
    extras_require={
        'test': [
            'pytest',
            'flake8',
            # Consider adding the flake8-docstrings plugin
        ],
    },

    #TODO Set it up to automatically generate the parsers from ebnf files after
    # installation. This may help:
    # https://stackoverflow.com/questions/1321270/how-to-extend-distutils-with-a-simple-post-install-script/1321345#1321345
    # which was linked to from:
    # https://stackoverflow.com/questions/14441955/how-to-perform-custom-build-steps-in-setup-py
    # Or it could potentially be done during the build step instead (see second
    # answer at second link)
    # Be careful not to break pip -e if possible

    entry_points={
        'console_scripts': [
            'mgen=smedl.mgen:main',
        ],
    },
)
