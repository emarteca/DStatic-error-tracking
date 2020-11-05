#!/bin/bash

projRoot=$1
projName=$2

# if there is no QLDBs folder yet, create it
if [ ! -d "QLDBs" ]; then
	mkdir QLDBs
fi

# make the QL DB and upgrade it, if it doesnt already exist

if [ ! -d "QLDBs/$projName" ]; then
	#export LGTM_INDEX_FILTERS='include:/'
	codeql database create --language=java --source-root $projRoot QLDBs/$projName
	codeql database upgrade QLDBs/$projName
fi

# run the query
codeql query run --database QLDBs/${projName} --output=${projName}_tempOut.bqrs $3
codeql bqrs decode --format=csv ${projName}_tempOut.bqrs > ${projName}_temp.csv
rm ${projName}_tempOut.bqrs
