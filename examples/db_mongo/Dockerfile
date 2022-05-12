FROM node:16.14.0 AS builder

WORKDIR /usr/src/app

COPY package*.json ./
COPY ./src src
COPY tsconfig.json .

COPY ./examples/db_mongo examples/db_mongo

RUN npm install && npm run tsc:build
RUN cd examples/db_mongo && npm install

RUN rm -rf examples/db_mongo/node_modules/abgp-js && \
    mkdir -p examples/db_mongo/node_modules/abgp-js && \
    cp -r dist examples/db_mongo/node_modules/abgp-js/dist && \
    cp package.json examples/db_mongo/node_modules/abgp-js && \
    cp package-lock.json examples/db_mongo/node_modules/abgp-js && \
    cd examples/db_mongo/node_modules/abgp-js && npm install --production

RUN cd examples/db_mongo && npm run build
###
# ---

# Running code under slim image (production part mostly)
FROM node:16.14.0-slim

## Clean new directory
WORKDIR /app

## We just need the build and package to execute the command
COPY --from=builder /usr/src/app/examples/db_mongo/dist build
COPY --from=builder /usr/src/app/examples/db_mongo/node_modules node_modules
ENTRYPOINT ["node"]
CMD ["build/index.js"]