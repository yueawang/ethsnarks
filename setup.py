import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="ethsnarks",
    version="0.0.1",
    author="HarryR",
    description="Python library for ethsnarks",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/HarryR/ethsnarks-python",
    packages=setuptools.find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: GNU Library or Lesser General Public License (LGPL)",
        "Operating System :: OS Independent",
    ],
    install_requires=[
        'py_ecc',
        'bitstring',
        'pysha3',
        'pyblake2'
    ]
)

