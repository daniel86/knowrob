#!/bin/bash

# source ros ws
source ${ROS_WS}/devel/setup.bash

# Start MongoDB and save data on working directory
MONGODB_URL=mongodb://127.0.0.1:27017
# Store MongoDB data under directory ${HOME}/data/db
mongod --fork --logpath ${HOME}/mongod.log

# jupyterlab UI workspace
jupyter lab workspaces import ${PWD}/binder/jupyterlab.jupyterlab-workspace

exec "$@"