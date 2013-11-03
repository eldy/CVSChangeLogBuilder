#!/bin/sh

cvs update
#cvs udpate -C


export GIT_DIR=/home/ldestailleur/git/cvschangelog/.git

git-cvsexportcommit IDCOMMIT

