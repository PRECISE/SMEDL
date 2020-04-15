"""A setuptools based setup module.

See:
https://packaging.python.org/en/latest/distributing.html
https://github.com/pypa/sampleproject
"""

# Always prefer setuptools over distutils
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

    # Versions should comply with PEP440.  For a discussion on single-sourcing
    # the version across setup.py and the project code, see
    # https://packaging.python.org/en/latest/single_source_version.html
    version=__about__['version'],

    description=__about__['summary'],
    long_description=long_description,

    # The project's main homepage.
    url=__about__['uri'],

    # Author details
    author=__about__['author'],
    author_email=__about__['email'],

    # Choose your license
    license=__about__['license'],

    # See https://pypi.python.org/pypi?%3Aaction=list_classifiers
    classifiers=[
        # How mature is this project? Common values are
        #   3 - Alpha
        #   4 - Beta
        #   5 - Production/Stable
        'Development Status :: 3 - Alpha',

        # Indicate who your project is intended for
        'Intended Audience :: Developers',

        # Pick your license as you wish (should match "license" above)
        #'License :: OSI Approved :: MIT License',

        # Specify the Python versions you support here. In particular, ensure
        # that you indicate whether you support Python 2, Python 3 or both.
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.5',
        'Programming Language :: Python :: 3.6',
        'Programming Language :: Python :: 3.7',
    ],

    # What does your project relate to?
    keywords='runtime-verification',

    # You can just specify the packages manually here if your project is
    # simple. Or you can use find_packages().
    #packages=find_packages(exclude=['contrib', 'docs', 'tests']),
    packages=[
        'smedl',
        'smedl.parser',
        'smedl.codegen',
        'smedl.structures',
        'smedl.codegen.static'
    ],

    # Alternatively, if you want to distribute just a my_module.py, uncomment
    # this:
    #   py_modules=["my_module"],

    # List run-time dependencies here.  These will be installed by pip when
    # your project is installed. For an analysis of "install_requires" vs pip's
    # requirements files see:
    # https://packaging.python.org/en/latest/requirements.html
    install_requires=[
        'tatsu>=4.4,<5',
        'Jinja2>=2.10',
        'importlib_resources>=1.1;python_version<"3.7"',
        'MarkupSafe>=0.23',
        'mccabe>=0.5',
        'nose2',
        'pyelftools',
        'pika',
        'libconf',
        'pyparsing',
    ],

    # List additional groups of dependencies here (e.g. development
    # dependencies). You can install these using the following syntax,
    # for example:
    # $ pip install -e .[dev,test]
    #     extras_require={
    #         'dev': ['check-manifest'],
    #         'test': ['coverage'],
    #     },

    # If there are data files included in your packages that need to be
    # installed, specify them here.  If using Python 2.6 or less, then these
    # have to be included in MANIFEST.in as well.
    package_data={
        '': ['*.c', '*.h'],
        'smedl': ['about.json'],
        #'smedl': ['about.json', 'c_style/*.c', 'c_style/*.h', 'c_style/*.cfg'],
    },

    # To provide executable scripts, use entry points in preference to the
    # "scripts" keyword. Entry points provide cross-platform support and allow
    # pip to create the appropriate form of executable for the target platform.
    entry_points={
        'console_scripts': [
            'mgen=smedl.mgen:main',
        ],
    },
)
