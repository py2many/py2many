#!/usr/bin/env python
from py14.transpiler import transpile
from flask import Flask, request, redirect, url_for, send_from_directory


app = Flask(__name__)
app.debug = True


@app.route('/')
def root():
    return app.send_static_file('index.html')


@app.route('/<path:path>')
def static_proxy(path):
    return app.send_static_file(path)


if __name__ == "__main__":
    app.run()
