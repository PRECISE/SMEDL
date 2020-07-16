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
    author_email=__about__['email'],
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

    entry_points={
        'console_scripts': [
            'mgen=smedl.mgen:main',
        ],
    },
)
