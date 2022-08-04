FROM node:16.14.0 AS builder

WORKDIR /usr/src/app

COPY package*.json ./
COPY ./src src
COPY tsconfig.json .

RUN npm install && npm run build && \
  rm -rf node_modules &&  \
  npm install --production

#### ---

# Running code under slim image (production part mostly)
FROM node:16.14.0-slim

## Clean new directory
WORKDIR /app

## We just need the build and package to execute the command
COPY --from=builder /usr/src/app/dist build
COPY --from=builder /usr/src/app/node_modules node_modules
ENTRYPOINT ["node"]
CMD ["build/index.js"]