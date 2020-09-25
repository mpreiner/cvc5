#!/bin/bash

git diff --name-only ${GITHUB_BASE_REF} ${GITHUB_SHA}
